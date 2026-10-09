/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.OrderType.FiniteUnion
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Essential rank and essential truncation

This file formalizes Lemma 2.12 and Definition 2.13, the first reduction of the proof of
Theorem A. For a nonempty well-ordered set of rationals of order type below `ω ^ ω`, some
integer closed truncation attains a greatest finite rank. The least integer cutoff attaining
that rank supplies a fixed reference point for estimates on larger truncations.

## Main definitions

* `PAdicOrderType.truncationRanks`: the natural numbers `r` for which some integer closed
  truncation has order type at least `ω ^ r`, the set `W_f` of Lemma 2.12.
* `PAdicOrderType.essentialRank`: the greatest attained rank, the essential rank `r(f)` of
  Lemma 2.12 (1).
* `PAdicOrderType.essentialTruncationPoint`: the least integer cutoff attaining that rank, the
  essential truncation point `B(f)` of Definition 2.13.

## Main statements

* `PAdicOrderType.essentialRank_spec`: the essential rank is attained and maximal
  (Lemma 2.12 (1)).
* `PAdicOrderType.typeLT_inter_Iic_lt_omega0_pow_essentialRank_succ`: every integer closed
  truncation has order type below `ω ^ (r + 1)` (Lemma 2.12 (2)).
* `PAdicOrderType.typeLT_le_omega0_of_essentialRank_eq_zero`: essential rank zero implies
  order type at most `ω`, because every bounded truncation is finite (Lemma 2.12 (3)).
* `PAdicOrderType.essentialTruncationPoint_spec`: the essential cutoff is attained and minimal
  (Definition 2.13).

## Implementation notes

Lemma 2.12 and Definition 2.13 are stated for the support of a nonzero p-adic Hahn series.
The definitions here apply to arbitrary nonempty well-ordered sets of rationals, including sets
with negative elements. Proof arguments ensure nonemptiness and the strict upper bound `ω ^ ω`.
-/

namespace PAdicOrderType

open Ordinal

/-- A well-ordered set of rationals with finite integer closed truncations has order
type at most `ω`. Counting predecessors gives a strictly monotone map into `ℕ`, as in the
proof of Lemma 2.12 (3). -/
theorem typeLT_le_omega0_of_forall_inter_Iic_finite {S : Set ℚ} [WellFoundedLT ↥S]
    (hfin : ∀ R : ℤ, (S ∩ Set.Iic (R : ℚ)).Finite) :
    typeLT ↥S ≤ omega0 := by
  classical
  have hpred : ∀ x : ↥S, (S ∩ Set.Iio (x : ℚ)).Finite := fun x =>
    (hfin ⌈(x : ℚ)⌉).subset fun y hy =>
      ⟨hy.1, Set.mem_Iic.mpr ((Set.mem_Iio.mp hy.2).le.trans (Int.le_ceil _))⟩
  let ψ : ↥S → ℕ := fun x => (hpred x).toFinset.card
  have hψ : StrictMono ψ := by
    intro x y hxy
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨x, ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]; exact ⟨x.2, hxy⟩
      · rw [Set.Finite.mem_toFinset]; exact fun h => lt_irrefl _ (Set.mem_Iio.mp h.2)
    · intro z hz
      rw [Set.Finite.mem_toFinset] at hz ⊢
      exact ⟨hz.1, Set.mem_Iio.mpr ((Set.mem_Iio.mp hz.2).trans hxy)⟩
  have h := Ordinal.typeLT_set_le_of_strictMono (γ := ℕ) ψ hψ
  simpa [Ordinal.type_nat_lt] using h

/-- An infinite well-ordered subset of `ℚ` has order type at least `ω`. -/
theorem omega0_le_typeLT_of_infinite {S : Set ℚ} [WellFoundedLT ↥S] (hS : S.Infinite) :
    omega0 ≤ typeLT ↥S := by
  by_contra hlt
  obtain ⟨m, hm⟩ := lt_omega0.mp (not_le.mp hlt)
  have hcard : Cardinal.mk ↥S < Cardinal.aleph0 := by
    have := congrArg Ordinal.card hm
    rw [Ordinal.card_type, Ordinal.card_nat] at this
    rw [this]
    exact Cardinal.natCast_lt_aleph0
  exact hS (Cardinal.lt_aleph0_iff_set_finite.mp hcard)

/-- The truncation `S ∩ (-∞, R]` of a well-ordered set is well-ordered. -/
instance instWellFoundedLTInterIic {S : Set ℚ} [WellFoundedLT ↥S] (R : ℚ) :
    WellFoundedLT ↥(S ∩ Set.Iic R) :=
  wellFoundedLT_of_subset Set.inter_subset_left

/-- The natural numbers `r` for which some integer closed truncation of `S` has
order type at least `ω ^ r`. For `S` the support of `f`, this is the set `W_f` of
Lemma 2.12. -/
def truncationRanks (S : Set ℚ) [WellFoundedLT ↥S] : Set ℕ :=
  {r | ∃ B : ℤ, omega0 ^ r ≤ typeLT ↥(S ∩ Set.Iic (B : ℚ))}

/-- Lemma 2.12 (1): a nonempty well-ordered set of order type below `ω ^ ω` has a greatest
attained truncation rank. Nonemptiness gives rank zero, and an upper bound by a finite power
of `ω` bounds the possible ranks. -/
theorem exists_isGreatest_truncationRanks {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) :
    ∃ r, IsGreatest (truncationRanks S) r := by
  classical
  obtain ⟨c, hc_lt, hc⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero isSuccLimit_omega0).mp hlt
  obtain ⟨N, rfl⟩ := lt_omega0.mp hc_lt
  have hbound : ∀ j ∈ truncationRanks S, j < N := by
    rintro j ⟨B, hB⟩
    have hpow : omega0 ^ (j : Ordinal) < omega0 ^ (N : Ordinal) := by
      rw [Ordinal.opow_natCast]
      exact lt_of_le_of_lt (hB.trans (typeLT_le_of_subset Set.inter_subset_left)) hc
    exact_mod_cast (opow_lt_opow_iff_right one_lt_omega0).mp hpow
  have hzero : 0 ∈ truncationRanks S := by
    obtain ⟨q, hq⟩ := hS
    refine ⟨⌈q⌉, ?_⟩
    rw [pow_zero]
    exact Order.one_le_iff_ne_zero.mpr
      (Ordinal.type_ne_zero_iff_nonempty.mpr ⟨⟨q, hq, Int.le_ceil q⟩⟩)
  refine ⟨Nat.findGreatest (· ∈ truncationRanks S) N, ?_, ?_⟩
  · exact Nat.findGreatest_spec (Nat.zero_le N) hzero
  · intro j hj
    exact Nat.le_findGreatest (hbound j hj).le hj

/-- The **essential rank** `r(f)` of Lemma 2.12 (1), for a nonempty well-ordered set of
order type below `ω ^ ω`: the greatest natural number `r` attained as a lower bound `ω ^ r`
for an integer closed truncation. The proof arguments ensure that this greatest rank
exists. -/
noncomputable def essentialRank {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) : ℕ :=
  (exists_isGreatest_truncationRanks hS hlt).choose

/-- Lemma 2.12 (1): the essential rank is attained by an integer closed truncation and is
at least every other attained rank. This property characterizes it uniquely. -/
theorem essentialRank_spec {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) :
    IsGreatest (truncationRanks S) (essentialRank hS hlt) :=
  (exists_isGreatest_truncationRanks hS hlt).choose_spec

/-- Lemma 2.12 (2): every integer closed truncation has order type strictly below
`ω ^ (r + 1)`, where `r` is the essential rank. Otherwise a larger rank would be attained. -/
theorem typeLT_inter_Iic_lt_omega0_pow_essentialRank_succ {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) (B : ℤ) :
    typeLT ↥(S ∩ Set.Iic (B : ℚ)) < omega0 ^ (essentialRank hS hlt + 1) := by
  by_contra hnot
  have := (essentialRank_spec hS hlt).2 ⟨B, not_lt.mp hnot⟩
  omega

/-- Lemma 2.12 (3): essential rank zero implies order type at most `ω`. All integer closed
truncations are finite, so every element has only finitely many predecessors. -/
theorem typeLT_le_omega0_of_essentialRank_eq_zero {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0)
    (hr : essentialRank hS hlt = 0) : typeLT ↥S ≤ omega0 := by
  refine typeLT_le_omega0_of_forall_inter_Iic_finite fun B ↦ ?_
  by_contra hinf
  have hbound := typeLT_inter_Iic_lt_omega0_pow_essentialRank_succ hS hlt B
  simp only [hr, zero_add, pow_one] at hbound
  exact (not_lt_of_ge (omega0_le_typeLT_of_infinite hinf)) hbound

/-- An integer cutoff attaining any natural rank is at least the minimum of the
original set. -/
private theorem min_le_of_omega0_pow_le {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) {r : ℕ} {B : ℤ}
    (hB : omega0 ^ r ≤ typeLT ↥(S ∩ Set.Iic (B : ℚ))) :
    Set.IsWF.min (show S.IsWF from wellFounded_lt) hS ≤ (B : ℚ) := by
  have hne : typeLT ↥(S ∩ Set.Iic (B : ℚ)) ≠ 0 :=
    (lt_of_lt_of_le (pow_pos omega0_pos r) hB).ne'
  obtain ⟨⟨q, hq, hqB⟩⟩ := Ordinal.type_ne_zero_iff_nonempty.mp hne
  exact (Set.IsWF.min_le (show S.IsWF from wellFounded_lt) hS hq).trans hqB

/-- There is a least integer cutoff attaining the essential rank, as required in
Definition 2.13. Such cutoffs exist by rank attainment and are bounded below by the minimum
of `S`. -/
theorem exists_isLeast_essentialTruncationPoint {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) :
    ∃ B, IsLeast {B : ℤ | omega0 ^ essentialRank hS hlt ≤
      typeLT ↥(S ∩ Set.Iic (B : ℚ))} B := by
  let cutoffs : Set ℤ := {B | omega0 ^ essentialRank hS hlt ≤
    typeLT ↥(S ∩ Set.Iic (B : ℚ))}
  have hne : cutoffs.Nonempty := (essentialRank_spec hS hlt).1
  have hbounded : BddBelow cutoffs := by
    refine ⟨⌊Set.IsWF.min (show S.IsWF from wellFounded_lt) hS⌋, ?_⟩
    intro B hB
    have hle := (Int.floor_le (Set.IsWF.min (show S.IsWF from wellFounded_lt) hS)).trans
      (min_le_of_omega0_pow_le hS hB)
    exact_mod_cast hle
  exact ⟨sInf cutoffs, Int.csInf_mem hne hbounded, fun B hB ↦ csInf_le hbounded hB⟩

/-- The **essential truncation point** `B(f)` of Definition 2.13: the least integer cutoff
whose closed truncation has order type at least `ω` raised to the essential rank. -/
noncomputable def essentialTruncationPoint {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) : ℤ :=
  (exists_isLeast_essentialTruncationPoint hS hlt).choose

/-- Definition 2.13: the essential truncation point attains the essential rank and is no
greater than any other integer cutoff attaining it. -/
theorem essentialTruncationPoint_spec {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) :
    IsLeast {B : ℤ | omega0 ^ essentialRank hS hlt ≤
      typeLT ↥(S ∩ Set.Iic (B : ℚ))} (essentialTruncationPoint hS hlt) :=
  (exists_isLeast_essentialTruncationPoint hS hlt).choose_spec

/-- The essential truncation point is at least the minimum of `S`. For a nonzero
Hahn series, this minimum is its additive valuation, so `B(f) ≥ v_p(f)` as noted after
Definition 2.13. -/
theorem min_le_essentialTruncationPoint {S : Set ℚ} [WellFoundedLT ↥S]
    (hS : S.Nonempty) (hlt : typeLT ↥S < omega0 ^ omega0) :
    Set.IsWF.min (show S.IsWF from wellFounded_lt) hS ≤ (essentialTruncationPoint hS hlt : ℚ) :=
  min_le_of_omega0_pow_le hS (essentialTruncationPoint_spec hS hlt).1

end PAdicOrderType
