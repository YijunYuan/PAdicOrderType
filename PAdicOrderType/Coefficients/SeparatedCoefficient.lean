/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateData
import PAdicOrderType.Coefficients.DirectPowerCoefficient
import PAdicOrderType.Interleaving.InterleavingEstimate

/-!
# Bounded separated coefficient estimate

This file proves Lemma 3.16. Let `H = coefficientFamily p D A` be a family of carry-free
coefficients over `K = ℚᶜᵘⁿ_[p,T]`, and let `B 0, B 1, …` be pairwise disjoint coordinate
blocks of a common cardinality `s`. Assume that every `d ∈ D` supported on the union of the
blocks is nonzero on at most `r ≥ 1` of them, and that for one fixed word `α₁ ⋯ α_r` of nonzero
valid letters every placement `ρ_{B j₁, α₁} + ⋯ + ρ_{B j_r, α_r}` (`j₁ < ⋯ < j_r`)
belongs to `D` with coefficient of multiplicative valuation `≥ γ₀`, where `γ₀ ≠ 0`. Then for
every `n : ℕ` there are `n * r` blocks `J` and a proper `u`, nonzero on each `B j` (`j ∈ J`)
and zero elsewhere, such that the coefficient `[X^u] H ^ n` is nonzero of
multiplicative valuation `≥ γ₀ ^ n * v (interleavingConstant n r)`.

The coefficient of every placement of every word of length `≤ r` is assumed
independent of the increasing block indices. In the application this follows
directly from QTR invariance under insertions of zeros. The finite family of
words of length `r` is evaluated using the coefficient estimate for interleavings.
At the maximal block count, each input supplies complete blocks, so its power
coefficient is the sum over ordered partitions
of those blocks.
The argument is carried out over an arbitrary field of characteristic zero with
a valuation (`exists_top_ray_coeff_of_valuation`); `exists_top_ray_coeff` is its
specialization to `ℚᶜᵘⁿ_[p,T]` with `Valued.v`. The invariance under increasing placements
is Lemma 3.12, the reduction to interleavings is Lemma 3.14, and the estimate for
interleavings is Lemma 3.15.
-/

namespace PAdicOrderType

open RamifiedCoefficients

attribute [local instance] letterLinearOrder

/-! ### Auxiliary lemmas -/

/-- There are finitely many words of length `r` over digit patterns of width `s`
whose entries are all below `p`. -/
lemma exists_finset_words (s p r : ℕ) :
    ∃ F : Finset (List (Fin s → ℕ)), ∀ w : List (Fin s → ℕ), w.length = r →
      (∀ e ∈ w, ∀ t, e t < p) → w ∈ F := by
  classical
  refine ⟨(wordsOfLen (Fintype.piFinset fun _ : Fin s => Finset.range p).toList r).toFinset, ?_⟩
  intro w hlen hdig
  apply List.mem_toFinset.mpr
  apply mem_wordsOfLen hlen
  intro e he
  rw [Finset.mem_toList, Fintype.mem_piFinset]
  exact fun t => Finset.mem_range.mpr (hdig e he t)

/-- The standard placement of the word `[α 0, …, α (r-1)]` along the blocks
`B 0, …, B (r-1)` is the sum of the placements of its letters. -/
lemma placeList_ofFn_range {s : ℕ} :
    ∀ {r : ℕ} (B : ℕ → Finset ℕ+) (α : Fin r → (Fin s → ℕ)),
      placeList B (List.ofFn α) (List.range r) = ∑ i : Fin r, placeAt (B (i : ℕ)) (α i) := by
  intro r
  induction r with
  | zero =>
    intro B α
    rw [List.ofFn_zero, placeList_nil, Finset.univ_eq_empty, Finset.sum_empty]
  | succ r ih =>
    intro B α
    rw [List.ofFn_succ, List.range_succ_eq_map, placeList_cons_cons, Fin.sum_univ_succ,
      ← placeList_comp B Nat.succ, ih (fun j => B (Nat.succ j)) (fun i => α i.succ)]
    rfl

/-! ### The quantitative top-ray coefficient -/

/-- **Bounded separated coefficient** (Lemma 3.16) over a characteristic-zero valued field.
Under the block-count bound, invariance under increasing placements, and a witness word
with coefficient valuation at least `γ₀ ≠ 0`, there is a proper vector occupying exactly
`n * r` blocks whose carry-free power coefficient is nonzero and has multiplicative
valuation at least `γ₀ ^ n * v (interleavingConstant n r)`. -/
theorem exists_top_ray_coeff_of_valuation {p : ℕ} [Fact (Nat.Prime p)] {K : Type*} [Field K]
    [CharZero K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {D : Set DigitSeries} {A : DigitSeries → K}
    {s : ℕ} {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j)) (hcard : ∀ i, (B i).card = s)
    {r : ℕ} (hr : 0 < r)
    (hhom : ∃ γ : List (Fin s → ℕ) → K,
      ∀ w : List (Fin s → ℕ), w.length ≤ r → (∀ e ∈ w, ∀ t, e t < p) →
        ∀ l : List ℕ, l.Pairwise (· < ·) → l.length = w.length →
          DigitCoefficients.extendMv (coefficientFamily p D A) (placeList B w l) = γ w)
    (hblocks : ∀ d ∈ D, (∀ i : ℕ+, d i ≠ 0 → ∃ j, i ∈ B j) →
      ∀ J : Finset ℕ, (∀ j ∈ J, ∃ i ∈ B j, d i ≠ 0) → J.card ≤ r)
    {α : Fin r → (Fin s → ℕ)} (hα0 : ∀ i, α i ≠ 0) (hαp : ∀ i t, α i t < p)
    {γ₀ : Γ₀} (hγ₀ : γ₀ ≠ 0)
    (hplace : ∀ jj : Fin r → ℕ, StrictMono jj →
      (∑ i, placeAt (B (jj i)) (α i)) ∈ D ∧
        γ₀ ≤ v (A ((∑ i, placeAt (B (jj i)) (α i)))))
    (n : ℕ) :
    ∃ (J : Finset ℕ) (u : {d : DigitSeries // d.IsP p}), J.card = n * r ∧
      (∀ i : ℕ+, u.1 i ≠ 0 → ∃ j ∈ J, i ∈ B j) ∧ (∀ j ∈ J, ∃ i ∈ B j, u.1 i ≠ 0) ∧
      (DigitCoefficients.power (coefficientFamily p D A) n) u ≠ 0 ∧
      γ₀ ^ n * v (interleavingConstant n r : K) ≤
        v ((DigitCoefficients.power (coefficientFamily p D A) n) u) := by
  classical
  have hp : 0 < p := Nat.Prime.pos Fact.out
  obtain ⟨γ, hkey⟩ := hhom
  -- The finite family of words of length exactly `r`.
  obtain ⟨F, hF⟩ := exists_finset_words s p r
  let Gfun : List (Fin s → ℕ) → K := fun w =>
    if w.length = r ∧ (∀ e ∈ w, e ≠ 0) ∧ (∀ e ∈ w, ∀ t, e t < p) then γ w else 0
  let G : (List (Fin s → ℕ)) →₀ K := Finsupp.onFinset F Gfun (by
    intro w hw
    by_contra hnot
    apply hw
    apply if_neg
    intro hcond
    exact hnot (hF w hcond.1 hcond.2.2))
  have hGapply : ∀ w, G w = Gfun w := fun w => Finsupp.onFinset_apply
  have hGcond : ∀ w ∈ G.support,
      w.length = r ∧ (∀ e ∈ w, e ≠ 0) ∧ (∀ e ∈ w, ∀ t, e t < p) := by
    intro w hw
    have h := Finsupp.mem_support_iff.mp hw
    rw [hGapply] at h
    by_contra hcond
    exact h (if_neg hcond)
  have hGlen : ∀ w ∈ G.support, w.length = r := fun w hw => (hGcond w hw).1
  have hGnz : ∀ w ∈ G.support, ∀ e ∈ w, e ≠ 0 := fun w hw => (hGcond w hw).2.1
  have hGlt : ∀ w ∈ G.support, ∀ e ∈ w, ∀ t, e t < p := fun w hw => (hGcond w hw).2.2
  have hA : ∀ u : {d : DigitSeries // d.IsP p}, coefficientFamily p D A u ≠ 0 →
      (∀ pos : ℕ+, u.1 pos ≠ 0 → ∃ j, pos ∈ B j) →
      (hitBlocks B (u.1)).card ≤ r := by
    intro u hu hcover
    have huD : u.1 ∈ D := by
      by_contra hnot
      exact hu (by rw [coefficientFamily_apply, if_neg hnot])
    apply hblocks u.1 huD hcover
    intro j hj
    exact (mem_hitBlocks hdisj (u.1) j).mp hj
  have hbase : ∀ (w : List (Fin s → ℕ)) (l : List ℕ), w.length = r →
      (∀ e ∈ w, e ≠ 0) → (∀ e ∈ w, ∀ t, e t < p) →
      l.Pairwise (· < ·) → l.length = w.length →
      DigitCoefficients.extendMv (coefficientFamily p D A) (placeList B w l) = G w := by
    intro w l hw hwnz hwlt hl hlen
    rw [hGapply, show Gfun w = γ w from if_pos ⟨hw, hwnz, hwlt⟩]
    exact hkey w hw.le hwlt l hl hlen
  -- The ray supplies a coefficient of sufficiently large valuation.
  set W₀ : List (Fin s → ℕ) := List.ofFn α with hW₀
  have hW₀len : W₀.length = r := List.length_ofFn
  have hW₀nz : ∀ e ∈ W₀, e ≠ 0 := by
    intro e he
    rw [hW₀, List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    exact hα0 i
  have hW₀lt : ∀ e ∈ W₀, ∀ t, e t < p := by
    intro e he
    rw [hW₀, List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    exact hαp i
  set x₀ : ℕ+ →₀ ℕ := ∑ i : Fin r, placeAt (B i) (α i)
  have hplaceW₀ : placeList B W₀ (List.range r) = x₀ := placeList_ofFn_range B α
  have hjj : x₀ ∈ D ∧ γ₀ ≤ v (A (x₀)) :=
    hplace (fun i => i) fun _ _ hab => hab
  have hx₀P : DigitSeries.IsP (x₀) p := by
    intro i
    have := placeList_lt hdisj hp W₀ (List.range r) hW₀lt List.pairwise_lt_range i
    rw [hplaceW₀] at this
    exact this
  have hGW₀ : G W₀ = A (x₀) := by
    rw [← hbase W₀ (List.range r) hW₀len hW₀nz hW₀lt List.pairwise_lt_range
      (by rw [List.length_range, hW₀len]), hplaceW₀,
      DigitCoefficients.extendMv_apply_of_isP _ hx₀P, coefficientFamily_apply, if_pos hjj.1]
  have hAx₀ : A (x₀) ≠ 0 := by
    intro h0
    have h := hjj.2
    rw [h0, map_zero] at h
    exact hγ₀ (le_antisymm h zero_le)
  have hγ : ∃ w ∈ G.support, γ₀ ≤ v (G w) :=
    ⟨W₀, Finsupp.mem_support_iff.mpr (by rw [hGW₀]; exact hAx₀), by rw [hGW₀]; exact hjj.2⟩
  -- The finite coefficient estimate for interleavings.
  obtain ⟨z, hzlen, hz0, hzval⟩ :=
    exists_interleaving_coefficient_valuation v hr hGlen hγ n
  have hzletters : ∀ e ∈ z, e ≠ 0 ∧ ∀ t, e t < p :=
    interleavingPower_support_letters K
      (fun w hw e he => ⟨hGnz w hw e he, hGlt w hw e he⟩) n z
      (Finsupp.mem_support_iff.mpr hz0)
  have hznz : ∀ e ∈ z, e ≠ 0 := fun e he => (hzletters e he).1
  have hzlt : ∀ e ∈ z, ∀ t, e t < p := fun e he => (hzletters e he).2
  -- At the maximal block count, each input supplies complete blocks.
  have hu₀P : DigitSeries.IsP ((placeList B z (List.range z.length))) p := fun i =>
    placeList_lt hdisj hp z (List.range z.length) hzlt List.pairwise_lt_range i
  have hcoeff :
      (DigitCoefficients.power (coefficientFamily p D A) n)
        ⟨(placeList B z (List.range z.length)), hu₀P⟩ =
      (interleavingPower K G n) z := by
    have h := power_coeff_placeList_eq_interleavingPower
      hdisj hcard (coefficientFamily p D A) G hA hGlen hbase n z
      (List.range z.length) hzlen hznz hzlt List.pairwise_lt_range List.length_range
    rwa [DigitCoefficients.extendMv_apply_of_isP _ hu₀P] at h
  refine ⟨Finset.range (n * r),
    ⟨(placeList B z (List.range z.length)), hu₀P⟩, Finset.card_range _,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_contra hnot
    refine hi (placeList_apply_eq_zero B z (List.range z.length) fun j hj hij => hnot ?_)
    exact ⟨j, Finset.mem_range.mpr
      (by rw [← hzlen]; exact List.mem_range.mp hj), hij⟩
  · intro j hj
    obtain ⟨pos, hpos, hval⟩ := exists_apply_ne_zero_of_mem hcard z (List.range z.length)
      hznz List.length_range j (List.mem_range.mpr (by rw [hzlen]; exact Finset.mem_range.mp hj))
    exact ⟨pos, hpos, hval⟩
  · rw [hcoeff]
    exact hz0
  · rw [hcoeff]
    exact hzval

/-- **Bounded separated coefficient** (Lemma 3.16) for the ramified coefficient field.
The carry-free power has a nonzero coefficient on exactly `n * r` blocks with multiplicative
valuation at least `γ₀ ^ n * Valued.v (interleavingConstant n r)`, under the block-count,
placement-invariance, and witness-coefficient hypotheses. -/
theorem exists_top_ray_coeff {p : ℕ} [Fact (Nat.Prime p)] {T : ℕ+}
    {D : Set DigitSeries} {A : DigitSeries → ℚᶜᵘⁿ_[p,(T : ℕ)]}
    {s : ℕ} {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j)) (hcard : ∀ i, (B i).card = s)
    {r : ℕ} (hr : 0 < r)
    (hhom : ∃ γ : List (Fin s → ℕ) → ℚᶜᵘⁿ_[p,(T : ℕ)],
      ∀ w : List (Fin s → ℕ), w.length ≤ r → (∀ e ∈ w, ∀ t, e t < p) →
        ∀ l : List ℕ, l.Pairwise (· < ·) → l.length = w.length →
          DigitCoefficients.extendMv (coefficientFamily p D A) (placeList B w l) = γ w)
    (hblocks : ∀ d ∈ D, (∀ i : ℕ+, d i ≠ 0 → ∃ j, i ∈ B j) →
      ∀ J : Finset ℕ, (∀ j ∈ J, ∃ i ∈ B j, d i ≠ 0) → J.card ≤ r)
    {α : Fin r → (Fin s → ℕ)} (hα0 : ∀ i, α i ≠ 0) (hαp : ∀ i t, α i t < p)
    {γ₀ : WithZero (Multiplicative ℤ)} (hγ₀ : γ₀ ≠ 0)
    (hplace : ∀ jj : Fin r → ℕ, StrictMono jj →
      (∑ i, placeAt (B (jj i)) (α i)) ∈ D ∧
        γ₀ ≤ Valued.v (A ((∑ i, placeAt (B (jj i)) (α i)))))
    (n : ℕ) :
    ∃ (J : Finset ℕ) (u : {d : DigitSeries // d.IsP p}), J.card = n * r ∧
      (∀ i : ℕ+, u.1 i ≠ 0 → ∃ j ∈ J, i ∈ B j) ∧ (∀ j ∈ J, ∃ i ∈ B j, u.1 i ≠ 0) ∧
      (DigitCoefficients.power (coefficientFamily p D A) n) u ≠ 0 ∧
      γ₀ ^ n * Valued.v (interleavingConstant n r : ℚᶜᵘⁿ_[p,(T : ℕ)]) ≤
        Valued.v ((DigitCoefficients.power (coefficientFamily p D A) n) u) :=
  exists_top_ray_coeff_of_valuation Valued.v hdisj hcard hr hhom hblocks hα0 hαp hγ₀ hplace n

end PAdicOrderType
