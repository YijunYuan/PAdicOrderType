/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.OrderType.FiniteRankExclusion
import Mathlib.Analysis.Normed.Group.Rat

/-!
# Support enlargement and finite initial segments

Adding a monomial above a bounded support gives a successor order type.
Together with Kedlaya's bound (Proposition 2.11) and finite-rank exclusion (Theorem 4.1),
this gives `finite_support_of_isAlgebraic_of_isBounded`, which is Proposition 4.2
(Theorem B).

The remaining lemmas relate order type at most `ω` to finite initial segments;
these are used in the strict Puiseux characterization (Proposition 4.3) assembled in
`PAdicOrderType.MainResults`.
-/

namespace PAdicOrderType

open TrustworthyKedlaya pAdicHahnSeries Bornology Ordinal

section SupportEnlargement

/-- Adding a suitable finite-support series to `f` enlarges its support by exactly one
prescribed point `n ∉ f.support`: there is an `h : 𝕃_[p]` with finite support such that
`(f + h).support = f.support ∪ {n}`. The witness is the Teichmüller monomial with
coefficient `1` at `n`, which plays the role of `p ^ (M + 1)` in the proof of
Proposition 4.2; since `f.coeff n = 0` there is no coefficient interaction, and
canonical-expansion uniqueness identifies the coefficient function of the sum. -/
private lemma exists_add_support_union_singleton {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) {n : ℚ} (hn : n ∉ f.support) :
    ∃ h : 𝕃_[p], h.support.Finite ∧ (f + h).support = f.support ∪ {n} := by
  classical
  let h : 𝕃_[p] := single n 1
  have hc : ∀ q, h.coeff q = if q = n then 1 else 0 := fun q => congrFun (coeff_single n 1) q
  have hs : h.support = {n} := by
    ext q
    simp only [mem_support_iff, hc, Set.mem_singleton_iff]
    split_ifs with hq <;> simp_all
  have hf : f.coeff n = 0 := not_not.mp hn
  have hsum : Function.support (f.coeff + h.coeff) = f.support ∪ {n} := by
    ext q
    simp only [Function.mem_support, Pi.add_apply, hc, Set.mem_union,
      Set.mem_singleton_iff, mem_support_iff]
    by_cases hq : q = n <;> simp [hq, hf]
  have hpwo : (Function.support (f.coeff + h.coeff)).IsPWO := by
    rw [hsum]
    exact (support_IsPWO f).union (Set.finite_singleton n).isPWO
  have heq := fromCoeff_add_of_disjoint_support f.coeff h.coeff
    (support_IsPWO f) (support_IsPWO h) hpwo (by
      intro q
      by_cases hq : q = n
      · exact Or.inl (hq ▸ hf)
      · exact Or.inr (by simp [hc, hq]))
  rw [fromCoeff_of_coeff_eq_self, fromCoeff_of_coeff_eq_self] at heq
  refine ⟨h, hs ▸ Set.finite_singleton n, ?_⟩
  change Function.support (f + h).coeff = _
  rw [heq, coeff_of_fromCoeff_eq_self, hsum]

/-- **The bounded-support corollary** (Proposition 4.2): a `ℚ_[p]`-algebraic
`p`-adic Hahn series with bounded support has finite support.

Add a monomial at a natural exponent strictly above the support. The resulting
algebraic series has a greatest support element, so its order type is a successor.
Kedlaya's bound (Proposition 2.11) and finite-rank exclusion (Theorem 4.1) rule out
`ω ^ ω`, and the successor
cannot equal `ω` either. Thus the enlarged support, and hence the original support,
has finite order type. -/
theorem finite_support_of_isAlgebraic_of_isBounded {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚ_[p] f) (hf2 : IsBounded f.support) :
    f.support.Finite := by
  -- extract a strict natural upper bound `n` of the bounded set `f.support`
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hf2
  obtain ⟨n, hnC⟩ := exists_nat_gt C
  have hSn : ∀ x ∈ f.support, x < (n : ℚ) := by
    intro x hx
    have h1 : (x : ℝ) ≤ ‖x‖ := by
      rw [← Rat.norm_cast_real, Real.norm_eq_abs]
      exact le_abs_self _
    have h2 : (x : ℝ) < (n : ℝ) := lt_of_le_of_lt (h1.trans (hC x hx)) hnC
    exact_mod_cast h2
  have hn_not : (n : ℚ) ∉ f.support := fun hmem => absurd (hSn _ hmem) (lt_irrefl _)
  -- enlarge the support by the single point `n`
  obtain ⟨h, hh_fin, hsupp⟩ := exists_add_support_union_singleton f hn_not
  have hg_alg : IsAlgebraic ℚ_[p] (f + h) :=
    hf1.add (pAdicHahnSeries.alg_of_fin_supp p h hh_fin)
  have hnmem : (n : ℚ) ∈ (f + h).support := by
    rw [hsupp]
    exact Set.mem_union_right _ (Set.mem_singleton _)
  have hmax : IsMax (⟨(n : ℚ), hnmem⟩ : (f + h).support) := by
    apply isTop_iff_isMax.mp
    intro x
    rcases (Set.ext_iff.mp hsupp x.val).mp x.property with hx | hx
    · exact (hSn x.val hx).le
    · exact (Set.mem_singleton_iff.mp hx).le
  obtain ⟨A, hA⟩ := type_lt_mem_range_succ_iff.mpr ⟨_, hmax⟩
  have hfinite : typeLT (f + h).support < omega0 := by
    have hdichotomy : typeLT (f + h).support ≤ omega0 ∨
        typeLT (f + h).support = omega0 ^ omega0 := by
      rcases (kedlaya_2001b_ordinal_bound p (f + h) hg_alg).lt_or_eq with hlt | heq
      · exact Or.inl (typeLT_support_le_omega0_of_lt_omega0_pow_omega0 (f + h) hg_alg hlt)
      · exact Or.inr heq
    rcases hdichotomy with hle | heq
    · exact hle.lt_of_ne (fun heq => isSuccLimit_omega0.succ_ne A (hA.trans heq))
    · exact ((isSuccLimit_opow one_lt_omega0 isSuccLimit_omega0).succ_ne A
        (hA.trans heq)).elim
  have hfin : (f + h).support.Finite := by
    apply Cardinal.lt_aleph0_iff_set_finite.mp
    simpa only [card_type] using (card_lt_aleph0.mpr hfinite)
  exact hfin.subset (by rw [hsupp]; exact Set.subset_union_left)

end SupportEnlargement

section FiniteInitialSegments

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- For an algebraic series of order type at most `ω`, every truncation is finite.
A bounded algebraic support is finite by Proposition 4.2; otherwise embed the support into `ℕ`
and bound each truncation by a later support point. This is the first step of the converse
direction in the proof of Proposition 4.3. -/
lemma finite_support_inter_Iio_of_typeLT_le_omega0 (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f)
    (hord : typeLT f.support ≤ omega0) (r : ℚ) : (f.support ∩ Set.Iio r).Finite := by
  classical
  by_cases hbd : BddAbove f.support
  · by_cases hne : f.support.Nonempty
    · have hbelow : BddBelow f.support :=
        ⟨(support_IsPWO f).isWF.min hne, fun q hq => (support_IsPWO f).isWF.min_le hne hq⟩
      obtain ⟨a, ha⟩ := hbelow
      obtain ⟨b, hb⟩ := hbd
      have hbounded : Bornology.IsBounded f.support := by
        apply isBounded_iff_forall_norm_le.mpr
        refine ⟨‖a‖ + ‖b‖, fun q hq => ?_⟩
        have haq : (a : ℝ) ≤ q := by exact_mod_cast ha hq
        have hqb : (q : ℝ) ≤ b := by exact_mod_cast hb hq
        rw [← Rat.norm_cast_real, Real.norm_eq_abs]
        rw [← Rat.norm_cast_real a, ← Rat.norm_cast_real b, Real.norm_eq_abs, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [neg_abs_le (a : ℝ), abs_nonneg (b : ℝ)],
          by linarith [le_abs_self (b : ℝ), abs_nonneg (a : ℝ)]⟩
      exact (finite_support_of_isAlgebraic_of_isBounded f hf hbounded).subset
        Set.inter_subset_left
    · simp [Set.not_nonempty_iff_eq_empty.mp hne]
  · obtain ⟨u, hu, hru⟩ := not_bddAbove_iff.mp hbd r
    obtain ⟨e⟩ := type_le_iff'.mp (hord.trans_eq type_nat_lt.symm)
    let g : ↥(f.support ∩ Set.Iio r) → Fin (e ⟨u, hu⟩) := fun q =>
      ⟨e ⟨q.val, q.property.1⟩, e.map_rel_iff.mpr (show q.val < u from q.property.2.trans hru)⟩
    have : Finite ↥(f.support ∩ Set.Iio r) := Finite.of_injective g (by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : f.support => z.val) (e.injective (congrArg Fin.val hab)))
    exact Set.toFinite _

/-- Counting predecessors embeds a support with finite initial segments into `ℕ`. In the
proof of Proposition 4.3, this shows that strict p-adic Puiseux series have support order type
at most `ω`. -/
lemma typeLT_support_le_omega0_of_finite_below (f : 𝕃_[p])
    (hf : ∀ r : ℚ, (f.support ∩ Set.Iio r).Finite) : typeLT f.support ≤ omega0 := by
  apply typeLT_le_omega0_of_forall_inter_Iic_finite
  intro R
  exact (hf ((R : ℚ) + 1)).subset fun q hq =>
    ⟨hq.1, lt_of_le_of_lt hq.2 (lt_add_one (R : ℚ))⟩

end FiniteInitialSegments

end PAdicOrderType
