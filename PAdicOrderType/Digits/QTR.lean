/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import TrustworthyKedlaya.MainResults

/-!
# Quasi-twist recurrence and closed truncations

Quasi-twist recurrence (QTR, Definition 2.5) expresses coefficient invariance under insertion
of a fixed number of zeros into sufficiently long zero gaps in base-p expansions. The support
lies in a rational set with bounded digit sums.

## Main definitions

* `PAdicOrderType.IsQTR`: the support and zero-insertion conditions for a coefficient function
  (Definition 2.5).

## Main statements

* `PAdicOrderType.QTR.twistSeq_eq_coeff`: twist-sequence values are coefficients at shifted digit
  expansions.
* `PAdicOrderType.QTR.recurrence_of_twist`: eventual periodicity of twist sequences gives the
  zero-insertion recurrence, condition (2) of Definition 2.5.
* `PAdicOrderType.isQTR_restrict`: restriction to an integer closed truncation preserves
  the same recurrence data, as used in the proofs of Corollary 2.10 and Lemma 3.9.

## Implementation notes

The digit sequences use zero-based indices: position `i` has weight `p ^ (-(i + 1))`.
The parameters `a`, `M`, and `N` are positive; `b` and `c` are natural numbers.
-/

@[expose] public section

namespace PAdicOrderType

open TrustworthyKedlaya LaurentSeries


/-- A **quasi-twist-recurrent** (QTR) coefficient function in the sense of Definition 2.5,
with scale `a`, lower slice bound `-b`, digit-sum bound `c`, zero-gap threshold `M`, and
insertion period `N`.

The support is well ordered and contained in `TrustworthyKedlaya.Sabc p a b c`.
For a point `(w - ∑ i, d i * p ^ (-(i + 1))) / a` with `w ≥ -b`, digits below `p`,
and digit sum at most `c`, inserting `N` zeros after any run of `M` zeros preserves
the coefficient. Digits use zero-based indices, so position `i` has weight
`p ^ (-(i + 1))`. -/
def IsQTR {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ → 𝔽ᵃ_[p])
    (a : ℕ+) (b c : ℕ) (M N : ℕ+) : Prop :=
  -- The support is a well-ordered subset of `ℚ`.
  (Function.support x).IsWF ∧
  -- Condition (1): the support is contained in `S_{a,b,c}`.
  (Function.support x ⊆ TrustworthyKedlaya.Sabc p a b c) ∧
  -- Condition (2): the `M`-zero-run ⇒ `N`-zero-insertion recurrence.
  ∀ (w : ℤ), -(b : ℤ) ≤ w → ∀ (d : ℕ →₀ ℕ), (∀ i, d i < p) →
      (d.sum fun _ v => v) ≤ c →
    ∀ (k : ℕ), (∀ i, k ≤ i → i < k + (M : ℕ) → d i = 0) →
      x ((1 / (a : ℚ)) * ((w : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))
        = x ((1 / (a : ℚ)) * ((w : ℚ) -
            (Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d).sum
              fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))

namespace QTR

/-- A twist-sequence value is the coefficient at the digit expansion obtained by
shifting the tail starting at position `j - 1` to the right by `n` places. This identifies
twist-sequence periodicity with invariance under insertion of zeros. -/
lemma twistSeq_eq_coeff {p : ℕ} [Fact (Nat.Prime p)] (x : HahnSeries ℚ (𝔽ᵃ_[p]))
    (m : ℤ) (a : ℕ+) (j : ℕ) (dig : ℕ →₀ ℕ) (n : ℕ) :
    TrustworthyKedlaya.twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n
      = x.coeff ((1 / (a : ℚ)) * ((m : ℚ) -
          (Finsupp.mapDomain (fun i => if i < j - 1 then i else i + n) dig).sum
            fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))) := by
  have hppos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hppos.ne'
  set s : ℕ → ℕ := fun i => if i < j - 1 then i else i + n with hs
  have hinj : Function.Injective s := by
    intro u v huv; simp only [hs] at huv; split_ifs at huv <;> omega
  have hDV : (Finsupp.mapDomain s dig).sum (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = (∑ i ∈ Finset.range (j - 1), (dig i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n : ℤ)) *
          ∑ i ∈ dig.support.filter (fun i => j - 1 ≤ i),
            (dig i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
    rw [Finsupp.sum_mapDomain_index_inj hinj]
    simp only [Finsupp.sum]
    rw [← Finset.sum_filter_add_sum_filter_not dig.support (fun i => i < j - 1)]
    congr 1
    · -- head: positions `< j-1` are fixed, fill in the zero digits to get `range (j-1)`
      trans (∑ i ∈ dig.support.filter (fun i => i < j - 1),
          (dig i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_filter] at hi
        have hsi : s i = i := by simp only [hs]; exact if_pos hi.2
        rw [hsi]
      · apply Finset.sum_subset
        · intro i hi
          rw [Finset.mem_filter] at hi; rw [Finset.mem_range]; exact hi.2
        · intro i hi hni
          rw [Finset.mem_range] at hi
          simp only [Finset.mem_filter, not_and, not_lt] at hni
          have hd0 : dig i = 0 := by
            by_contra h
            have := hni (Finsupp.mem_support_iff.mpr h); omega
          rw [hd0]; simp
    · -- tail: positions `≥ j-1` are shifted right by `n`, factoring out `p^{-n}`
      simp only [not_lt]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨_, hi2⟩ := hi
      have hsi : s i = i + n := by simp only [hs]; exact if_neg (by omega)
      have hpow : (p : ℚ) ^ (-(((i + n : ℕ) : ℤ)) + -1)
          = (p : ℚ) ^ (-(n : ℤ)) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
        rw [← zpow_add₀ hp0]; congr 1; push_cast; ring
      rw [hsi]
      rw [show (-(((i + n : ℕ) : ℤ) + 1)) = (-(((i + n : ℕ) : ℤ)) + -1) by ring, hpow]
      ring
  simp only [TrustworthyKedlaya.twistSeq]
  congr 1
  rw [hDV]; ring

/-- Shifting all digit positions at or beyond a threshold to the right is injective. -/
lemma shift_injective (k t : ℕ) :
    Function.Injective (fun i : ℕ => if i < k then i else i + t) := by
  intro a b hab; simp only at hab; split_ifs at hab <;> omega

/-- After inserting at least `M` zeros at position `k`, inserting a further `N` zeros
at position `k + M` is the same as inserting `n + N` zeros at position `k`. -/
lemma shift_comp_shift {k M N n : ℕ} (hMn : M ≤ n) (i : ℕ) :
    (fun i => if i < k + M then i else i + N) ((fun i => if i < k then i else i + n) i)
      = (if i < k then i else i + (n + N)) := by
  simp only
  split_ifs <;> omega

/-- Successive zero insertions compose to one longer tail shift when the first
insertion has length at least `M`. This is the digit-sequence form of
`PAdicOrderType.QTR.shift_comp_shift`. -/
lemma mapDomain_insert_shift {k M N n : ℕ} (hMn : M ≤ n) (dig : ℕ →₀ ℕ) :
    Finsupp.mapDomain (fun i => if i < k + M then i else i + N)
        (Finsupp.mapDomain (fun i => if i < k then i else i + n) dig)
      = Finsupp.mapDomain (fun i => if i < k then i else i + (n + N)) dig := by
  rw [← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr (fun i _ => shift_comp_shift hMn i)

/-- Inserting zeros preserves a positive upper bound on all digit values. -/
lemma shift_mapDomain_lt {p : ℕ} (hp : 0 < p) (k t : ℕ) (dig : ℕ →₀ ℕ)
    (hdig : ∀ i, dig i < p) (i : ℕ) :
    (Finsupp.mapDomain (fun i => if i < k then i else i + t) dig) i < p := by
  by_cases h : i ∈ Set.range (fun i : ℕ => if i < k then i else i + t)
  · obtain ⟨j, hj⟩ := h
    rw [← hj, Finsupp.mapDomain_apply (shift_injective k t)]; exact hdig j
  · rw [Finsupp.mapDomain_of_notMem_range _ _ h]; exact hp

/-- Inserting zeros preserves the sum of the digit values. -/
lemma shift_mapDomain_sum (k t : ℕ) (dig : ℕ →₀ ℕ) :
    (Finsupp.mapDomain (fun i => if i < k then i else i + t) dig).sum (fun _ v => v)
      = dig.sum (fun _ v => v) := by
  rw [Finsupp.sum_mapDomain_index_inj (shift_injective k t)]

/-- Eventual periodicity of the twist sequences gives the zero-insertion recurrence
(Definition 2.5 (2)) with the same threshold `M` and period `N`. Collapse a run of `M` zeros,
then compare the twist values at shifts `M` and `M + N`. -/
lemma recurrence_of_twist {p : ℕ} [Fact (Nat.Prime p)] (x : HahnSeries ℚ (𝔽ᵃ_[p]))
    (a : ℕ+) (b c : ℕ) (M N : ℕ+)
    (htwist : ∀ m : ℤ, m ≥ -(b : ℤ) →
        ∀ (j : ℕ) (dig : ℕ →₀ ℕ), 0 < j → (∀ i, dig i < p) → (dig.sum fun _ v => v) ≤ c →
          ∀ n : ℕ, (M : ℕ) ≤ n →
            twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig (n + (N : ℕ))
              = twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n) :
    ∀ (w : ℤ), -(b : ℤ) ≤ w → ∀ (d : ℕ →₀ ℕ), (∀ i, d i < p) → (d.sum fun _ v => v) ≤ c →
      ∀ (k : ℕ), (∀ i, k ≤ i → i < k + (M : ℕ) → d i = 0) →
        x.coeff ((1 / (a : ℚ)) * ((w : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))
          = x.coeff ((1 / (a : ℚ)) * ((w : ℚ) -
              (Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d).sum
                fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))) := by
  intro w hw d hdp hdc k hgap
  have hppos : 0 < p := (Fact.out : Nat.Prime p).pos
  -- The tail-shift collapsing the length-`M` gap at `k`.
  have hsinj : Function.Injective (fun i : ℕ => if i < k then i else i + (M : ℕ)) :=
    shift_injective k (M : ℕ)
  -- `d` is supported in the range of the shift, because it vanishes on the gap `[k, k+M)`.
  have hrange : ↑d.support ⊆ Set.range (fun i : ℕ => if i < k then i else i + (M : ℕ)) := by
    intro i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    rcases lt_or_ge i k with hik | hik
    · exact ⟨i, by simp only [if_pos hik]⟩
    · rcases lt_or_ge i (k + (M : ℕ)) with hik2 | hik2
      · exact absurd (hgap i hik hik2) hi
      · exact ⟨i - (M : ℕ), by simp only [if_neg (show ¬ i - (M:ℕ) < k by omega)]; omega⟩
  -- Collapse the gap.
  set dig : ℕ →₀ ℕ :=
    Finsupp.comapDomain (fun i : ℕ => if i < k then i else i + (M : ℕ)) d hsinj.injOn with hdigdef
  have hmap : Finsupp.mapDomain (fun i : ℕ => if i < k then i else i + (M : ℕ)) dig = d :=
    Finsupp.mapDomain_comapDomain _ hsinj d hrange
  -- Side conditions for `htwist`.
  have hdig_lt : ∀ i, dig i < p := by
    intro i; rw [hdigdef, Finsupp.comapDomain_apply]; exact hdp _
  have hdig_sum : (dig.sum fun _ v => v) ≤ c := by
    have h := shift_mapDomain_sum k (M : ℕ) dig
    rw [hmap] at h; rw [← h]; exact hdc
  -- Apply the twist period at shift `M`.
  have key := htwist w hw (k + 1) dig (Nat.succ_pos k) hdig_lt hdig_sum (M : ℕ) le_rfl
  -- Rewrite both twist values as coefficients via the bridge lemma `twistSeq_eq_coeff`.
  rw [twistSeq_eq_coeff x w a (k + 1) dig ((M : ℕ) + (N : ℕ)),
      twistSeq_eq_coeff x w a (k + 1) dig (M : ℕ)] at key
  simp only [Nat.add_sub_cancel] at key
  -- `mapDomain s_{k,M} dig = d` and `mapDomain s_{k,M+N} dig = mapDomain t_{k,M,N} d`.
  rw [hmap] at key
  have hcollapse :
      Finsupp.mapDomain (fun i => if i < k then i else i + ((M : ℕ) + (N : ℕ))) dig
        = Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d := by
    rw [← hmap]; exact (mapDomain_insert_shift (le_refl (M : ℕ)) dig).symm
  rw [hcollapse] at key
  exact key.symm

/-- A finite base-p fractional expansion with all digits below `p` has value below `1`. -/
lemma digitValue_lt_one {p : ℕ} (hp : 1 < p) (d : ℕ →₀ ℕ) (hd : ∀ i, d i < p) :
    (d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) < 1 := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range d.support
  rw [Finsupp.sum_of_support_subset d hn _ (by intro i _; simp)]
  -- Bound the partial sum over `range m` by `1 - p^{-m}` by induction on `m`.
  have hbound : ∀ m, (∑ i ∈ Finset.range m, (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      ≤ 1 - (p : ℚ) ^ (-(m : ℤ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have ht : (0 : ℚ) < (p : ℚ) ^ (-((m : ℤ) + 1)) := zpow_pos hp0 _
      have hdm : (d m : ℚ) ≤ (p : ℚ) - 1 := by
        have : (d m : ℚ) + 1 ≤ (p : ℚ) := by exact_mod_cast hd m
        linarith
      have hrel : (p : ℚ) ^ (-((m : ℤ) + 1)) * (p : ℚ) = (p : ℚ) ^ (-(m : ℤ)) := by
        rw [← zpow_add_one₀ (ne_of_gt hp0)]; congr 1; ring
      have key : (d m : ℚ) * (p : ℚ) ^ (-((m : ℤ) + 1))
          ≤ (p : ℚ) ^ (-(m : ℤ)) - (p : ℚ) ^ (-((m : ℤ) + 1)) := by
        rw [← hrel]
        calc (d m : ℚ) * (p : ℚ) ^ (-((m : ℤ) + 1))
            ≤ ((p : ℚ) - 1) * (p : ℚ) ^ (-((m : ℤ) + 1)) :=
              mul_le_mul_of_nonneg_right hdm ht.le
          _ = (p : ℚ) ^ (-((m : ℤ) + 1)) * (p : ℚ) - (p : ℚ) ^ (-((m : ℤ) + 1)) := by ring
      have hcast : (-(((m + 1 : ℕ)) : ℤ)) = (-((m : ℤ) + 1)) := by push_cast; ring
      rw [hcast]
      linarith [ih, key]
  calc (∑ i ∈ Finset.range n, (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      ≤ 1 - (p : ℚ) ^ (-(n : ℤ)) := hbound n
    _ < 1 := by have := zpow_pos hp0 (-(n : ℤ)); linarith

/-- Inserting zeros into a finite fractional digit expansion does not increase its
value: every nonzero digit moves to a position with no larger weight. -/
lemma digitValue_mapDomain_le {p : ℕ} (hp : 1 ≤ (p : ℚ)) (d : ℕ →₀ ℕ) (k M N : ℕ) :
    ((Finsupp.mapDomain (fun i => if i < k + M then i else i + N) d).sum
        fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      ≤ d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
  have hinj : Function.Injective (fun i : ℕ => if i < k + M then i else i + N) := by
    intro a b hab
    simp only at hab
    split_ifs at hab <;> omega
  rw [Finsupp.sum_mapDomain_index_inj hinj]
  apply Finsupp.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply zpow_le_zpow_right₀ hp
  split_ifs <;> push_cast <;> omega

end QTR

open QTR

/-- Restricting a QTR function to exponents at most an integer `r` preserves the same
recurrence data. Zero insertion preserves the integer slice, so it respects this cutoff.
This is the restriction step in the proofs of Corollary 2.10 and Lemma 3.9. -/
theorem isQTR_restrict {p : ℕ} [Fact (Nat.Prime p)] {x : ℚ → 𝔽ᵃ_[p]}
    {a : ℕ+} {b c : ℕ} {M N : ℕ+} (h : IsQTR x a b c M N) (r : ℤ) :
    IsQTR (fun q => if q ≤ (r : ℚ) then x q else 0) a b c M N := by
  obtain ⟨hwf, hsupp, hrec⟩ := h
  have hpp : Nat.Prime p := Fact.out
  have hp1' : 1 < p := hpp.one_lt
  have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp1'.le
  have a_pos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  -- support of the restriction is contained in support of `x`
  have hsub : Function.support (fun q => if q ≤ (r : ℚ) then x q else 0) ⊆ Function.support x := by
    intro q hq
    rw [Function.mem_support] at hq ⊢
    intro hx0
    apply hq
    simp only [hx0, ite_self]
  refine ⟨hwf.mono hsub, subset_trans hsub hsupp, ?_⟩
  intro w hw d hdp hdc k hk
  dsimp only
  -- abbreviations for the two digit-string values
  set Vd : ℚ := d.sum (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) with hVdeq
  set Vd' : ℚ := (Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d).sum
      (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) with hVd'eq
  -- value facts: `Vd' ≤ Vd` (insertion shrinks), `Vd < 1` (digit bound), `0 ≤ Vd'`.
  have hmono : Vd' ≤ Vd := by
    rw [hVdeq, hVd'eq]; exact digitValue_mapDomain_le hp1 d k (M : ℕ) (N : ℕ)
  have hVd_lt : Vd < 1 := by rw [hVdeq]; exact digitValue_lt_one hp1' d hdp
  have hVd'_nonneg : (0 : ℚ) ≤ Vd' := by
    rw [hVd'eq]; apply Finsupp.sum_nonneg; intro i _; positivity
  -- `q ≤ q'`: inserting zeros pushes the point to the right.
  have hqq' : (1 / (a : ℚ)) * ((w : ℚ) - Vd) ≤ (1 / (a : ℚ)) * ((w : ℚ) - Vd') :=
    mul_le_mul_of_nonneg_left (by linarith [hmono]) (one_div_pos.mpr a_pos).le
  by_cases hqr : (1 / (a : ℚ)) * ((w : ℚ) - Vd) ≤ (r : ℚ)
  · -- Case `q ≤ r`. Show `q' ≤ r` too, then reduce to clause (2) for `x`.
    -- From `q ≤ r`: `w - Vd ≤ a r`.
    have h1 : (w : ℚ) - Vd ≤ (a : ℚ) * (r : ℚ) := by
      have h0 := mul_le_mul_of_nonneg_left hqr a_pos.le
      rwa [← mul_assoc, mul_one_div, div_self (ne_of_gt a_pos), one_mul] at h0
    -- Integer rounding: `w - Vd ≤ a r` with `0 ≤ Vd < 1` and `a r ∈ ℤ` give `w ≤ a r`.
    have h2 : (w : ℚ) ≤ (a : ℚ) * (r : ℚ) := by
      have h3 : (w : ℚ) < (a : ℚ) * (r : ℚ) + 1 := by linarith [hVd_lt]
      have hcast : (a : ℚ) * (r : ℚ) = (((a : ℕ) : ℤ) * r : ℤ) := by push_cast; ring
      rw [hcast] at h3 ⊢
      have h4 : w < ((a : ℕ) : ℤ) * r + 1 := by exact_mod_cast h3
      exact_mod_cast (show w ≤ ((a : ℕ) : ℤ) * r by omega)
    -- Hence `aq' = w - Vd' ≤ w ≤ a r`, so `q' ≤ r`.
    have hq'r : (1 / (a : ℚ)) * ((w : ℚ) - Vd') ≤ (r : ℚ) := by
      have h5 : (w : ℚ) - Vd' ≤ (a : ℚ) * (r : ℚ) := by linarith [hVd'_nonneg, h2]
      calc (1 / (a : ℚ)) * ((w : ℚ) - Vd')
          ≤ (1 / (a : ℚ)) * ((a : ℚ) * (r : ℚ)) :=
            mul_le_mul_of_nonneg_left h5 (one_div_pos.mpr a_pos).le
        _ = (r : ℚ) := by
            rw [← mul_assoc, one_div_mul_cancel (ne_of_gt a_pos), one_mul]
    rw [if_pos hqr, if_pos hq'r, hVdeq, hVd'eq]
    exact hrec w hw d hdp hdc k hk
  · -- Case `q > r`. Then `q' ≥ q > r`, so both restricted values vanish.
    have hq'r : ¬ (1 / (a : ℚ)) * ((w : ℚ) - Vd') ≤ (r : ℚ) := fun hle => hqr (le_trans hqq' hle)
    rw [if_neg hqr, if_neg hq'r]

end PAdicOrderType
