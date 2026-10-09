/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import PAdicOrderType.Coefficients.Ramified

/-!
# Ramified Hahn lifts and null series

Hahn series with coefficients in the ramified Witt-vector ring admit coset sums along
exponents differing by multiples of `1/T`. A series is null when all these weighted
coset sums converge to zero. Null series form an ideal, and extending coefficients from
the unramified ring preserves and reflects this condition. This is the ramified analogue of
the null series of Section 2.1, used in the proof of Proposition 3.4.

## Main definitions

* `PAdicOrderType.RamifiedCoefficients.TLiftedPAdicHahnSeries`: rational-exponent Hahn series
  with ramified integral coefficients.
* `PAdicOrderType.RamifiedCoefficients.TLiftedPAdicHahnSeries.fromCoeff`: the coefficientwise
  Teichmüller lift.
* `PAdicOrderType.RamifiedCoefficients.IsTNullSeries`: vanishing of every weighted coset sum.
* `PAdicOrderType.RamifiedCoefficients.TNullSeriesIdeal`: the ideal of null series.

## Main statements

* `PAdicOrderType.RamifiedCoefficients.TNullSeriesIdeal_inter_image`: a lifted series is null
  after coefficient extension if and only if it was null before extension.

## Implementation notes

Coset sums take values in the complete ramified fraction field. Splitting an integer index
into residue classes modulo `T` relates these sums to the original integer-coset sums, as in
the summation over `0 ≤ j < T` in the proof of Proposition 3.4.
-/

@[expose] public section

namespace PAdicOrderType

open WittVector TrustworthyKedlaya


namespace RamifiedCoefficients

variable (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ) [NeZero T]

/-- Rational-exponent Hahn series with coefficients in the ramified integral ring
`ℤᶜᵘⁿ_[p,T]`. -/
abbrev TLiftedPAdicHahnSeries : Type _ := HahnSeries ℚ (ℤᶜᵘⁿ_[p,T])

end RamifiedCoefficients

namespace RamifiedCoefficients.TLiftedPAdicHahnSeries

variable (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ) [NeZero T]

/-- Lift a coefficient function with well-ordered support by applying the
Teichmüller map and then the inclusion into the ramified coefficient ring. -/
noncomputable def fromCoeff (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
    TLiftedPAdicHahnSeries p T where
  coeff n := OQpCUn_embd p T (teichmuller p (s n))
  isPWO_support' := by
    apply hspwo.mono
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hsn
    apply hn
    rw [hsn, WittVector.teichmuller_zero, map_zero]

end RamifiedCoefficients.TLiftedPAdicHahnSeries

namespace RamifiedCoefficients

variable (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ) [NeZero T]

/-- The natural ring inclusion `LiftedPAdicHahnSeries p ↪ TLiftedPAdicHahnSeries p T`,
obtained by applying `OQpCUn_embd` coefficient-wise. -/
noncomputable def Lifted_to_TLifted :
    LiftedPAdicHahnSeries p →+* TLiftedPAdicHahnSeries p T where
  toFun x := x.map (OQpCUn_embd p T : ℤᶜᵘⁿ_[p] →+* ℤᶜᵘⁿ_[p,T])
  map_zero' := by
    change HahnSeries.map 0 (OQpCUn_embd p T) = 0
    exact HahnSeries.map_zero (OQpCUn_embd p T : ZeroHom (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]))
  map_one' := HahnSeries.map_one (OQpCUn_embd p T).toMonoidWithZeroHom
  map_add' x y := by
    change HahnSeries.map (x + y) (OQpCUn_embd p T) =
      HahnSeries.map x (OQpCUn_embd p T) + HahnSeries.map y (OQpCUn_embd p T)
    exact HahnSeries.map_add (OQpCUn_embd p T : ℤᶜᵘⁿ_[p] →+ ℤᶜᵘⁿ_[p,T])
  map_mul' x y := HahnSeries.map_mul (OQpCUn_embd p T).toNonUnitalRingHom

/-- Only finitely many nonzero coefficients on the coset `g + (1/T)ℤ` occur at
exponents at most `M`. Well-ordered support bounds the integer indices below, and the
cutoff bounds them above. -/
abbrev TfiniteBelow (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (M : ℕ) :
    Set.Finite {n : ℤ | g + (n : ℚ) / T ≤ M ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset :
        {n : ℤ | g + (n : ℚ) / T ≤ M ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} ⊆
          Set.Icc (⌈(T : ℚ) * (m - g)⌉ : ℤ) ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
      intro n hn
      have hm_le : m ≤ g + (n : ℚ) / T :=
        x.isWF_support.min_le hs <| (HahnSeries.mem_support x _).2 hn.2
      have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
        rw [mul_div_assoc']; field_simp
      have hlower : (⌈(T : ℚ) * (m - g)⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        have h1 : m - g ≤ (n : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (m - g) ≤ (T : ℚ) * ((n : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        rw [hT_eq] at h2
        exact_mod_cast h2
      have hupper : n ≤ ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
        apply Int.le_floor.mpr
        have h1 : (n : ℚ) / T ≤ (M : ℚ) - g := by linarith [hn.1]
        have h2 : (T : ℚ) * ((n : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        rw [hT_eq] at h2
        exact_mod_cast h2
      exact ⟨hlower, hupper⟩
    exact ((Set.finite_Icc _ _).subset hsubset)
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | g + (n : ℚ) / T ≤ M ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + (n : ℚ) / T)]
    simp [hset]

open Topology Filter in
/-- A **ramified null series**: for every rational `g`, the weighted sum of
coefficients at `g + n / T`, with weight `(pInvTQ p T) ^ n`, converges to zero as the
upper exponent cutoff tends to infinity. The sums are taken in `ℚᶜᵘⁿ_[p,T]`. This adapts the
null series of Section 2.1 to the coefficient ring `Z̆_{p,T}`. -/
def IsTNullSeries (x : TLiftedPAdicHahnSeries p T) : Prop :=
  ∀ g : ℚ, Filter.Tendsto (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
      (pInvTQ p T) ^ (n.val : ℤ) *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) atTop (𝓝 0)

/-- Only finitely many integer indices `n ≤ K` have a nonzero coefficient at
`g + n / T`. -/
private abbrev TfiniteBelowInt
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (K : ℤ) :
    Set.Finite {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset :
        {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} ⊆
          Set.Icc (⌈(T : ℚ) * (m - g)⌉ : ℤ) K := by
      intro n hn
      have hm_le : m ≤ g + (n : ℚ) / T :=
        x.isWF_support.min_le hs <| (HahnSeries.mem_support x _).2 hn.2
      have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
        rw [mul_div_assoc']; field_simp
      have hlower : (⌈(T : ℚ) * (m - g)⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        have h1 : m - g ≤ (n : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (m - g) ≤ (T : ℚ) * ((n : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        rw [hT_eq] at h2
        exact_mod_cast h2
      exact ⟨hlower, hn.1⟩
    exact ((Set.finite_Icc _ _).subset hsubset)
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + (n : ℚ) / T)]
    simp [hset]

/-- The weighted coefficient sum on the coset of `g` through integer index `K`,
with weight `(pInvTQ p T) ^ n` at exponent `g + n / T`. -/
private noncomputable def TintPartial
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (K : ℤ) : ℚᶜᵘⁿ_[p,T] :=
  ∑ n : Set.Finite.toFinset (TfiniteBelowInt p T x g K),
    (pInvTQ p T) ^ (n.1 : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.1 : ℚ) / T))

/-- An integral coefficient multiplied by the `n`-th power of the uniformizer has
multiplicative valuation at most `ofAdd (-n)`. -/
private lemma Tvalued_v_term_le (a : ℤᶜᵘⁿ_[p,T]) (n : ℤ) :
    Valued.v ((pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a) ≤
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_pInvT_zpow]
  have h_alg : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one a
  calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a)
      ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
        mul_le_mul' (le_refl _) h_alg
    _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _

/-- The difference of two nested weighted partial sums is the sum over the
additional indices. -/
private lemma TintPartial_diff_eq_sdiff_sum
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (K K' : ℤ) (h : K ≤ K') :
    TintPartial p T x g K' - TintPartial p T x g K =
      ∑ n ∈ (Set.Finite.toFinset (TfiniteBelowInt p T x g K') \
              Set.Finite.toFinset (TfiniteBelowInt p T x g K)),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) := by
  have hsub : Set.Finite.toFinset (TfiniteBelowInt p T x g K) ⊆
      Set.Finite.toFinset (TfiniteBelowInt p T x g K') := by
    intro n hn
    have hn_mem : n ∈ {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} :=
      (Set.Finite.mem_toFinset _).mp hn
    exact (Set.Finite.mem_toFinset _).mpr ⟨le_trans hn_mem.1 h, hn_mem.2⟩
  have e1 : TintPartial p T x g K' = ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x g K'),
      (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T x g K'))
      (f := fun m : ℤ => (pInvTQ p T) ^ m *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (m : ℚ) / T)))
  have e2 : TintPartial p T x g K = ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x g K),
      (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T x g K))
      (f := fun m : ℤ => (pInvTQ p T) ^ m *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (m : ℚ) / T)))
  rw [e1, e2, ← Finset.sum_sdiff hsub, add_sub_cancel_right]

/-- The difference of weighted partial sums with index cutoffs `K₁ ≤ K₂` has
multiplicative valuation at most `ofAdd (-(K₁ + 1))`. -/
private lemma Tpartial_sum_valuation_cauchy
    (x : TLiftedPAdicHahnSeries p T) (g' : ℚ) (K₁ K₂ : ℤ) (h : K₁ ≤ K₂) :
    Valued.v (TintPartial p T x g' K₂ - TintPartial p T x g' K₁) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [TintPartial_diff_eq_sdiff_sum p T x g' K₁ K₂ h]
  apply Valuation.map_sum_le
  intro n hn
  have hn_mem : n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x g' K₂) ∧
      n ∉ Set.Finite.toFinset (TfiniteBelowInt p T x g' K₁) := Finset.mem_sdiff.mp hn
  have hn1 : n ≤ K₂ ∧ x.coeff (g' + (n : ℚ) / T) ≠ 0 :=
    (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x g' K₂)).mp hn_mem.1
  have hn2 : ¬ (n ≤ K₁ ∧ x.coeff (g' + (n : ℚ) / T) ≠ 0) := by
    intro h'
    exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x g' K₁)).mpr h')
  have hn_gt : K₁ < n := by
    by_contra hle
    push Not at hle
    exact hn2 ⟨hle, hn1.2⟩
  have h1 := Tvalued_v_term_le p T (x.coeff (g' + (n : ℚ) / T)) n
  have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_le_coe]
    exact Multiplicative.ofAdd_le.mpr (by omega)
  exact h1.trans h2

/-- Truncation at exponent `M` agrees with truncation at integer index
`⌊T * (M - g)⌋` on the coset of `g`. -/
private lemma TpartialSum_eq_intPartial
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (M : ℕ) :
    (∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) =
      TintPartial p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hT_eq : ∀ n : ℤ, (T : ℚ) * ((n : ℚ) / T) = n := by
    intro n; rw [mul_div_assoc']; field_simp
  have hset_eq : Set.Finite.toFinset (TfiniteBelow p T x g M) =
      Set.Finite.toFinset
        (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋) := by
    ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hle, hne⟩
      refine ⟨?_, hne⟩
      have h1 : (n : ℚ) / T ≤ (M : ℚ) - g := by linarith
      have h2 : (T : ℚ) * ((n : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
        mul_le_mul_of_nonneg_left h1 hT_pos.le
      rw [hT_eq n] at h2
      have h3 : (n : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := h2
      exact Int.le_floor.mpr h3
    · rintro ⟨hle, hne⟩
      refine ⟨?_, hne⟩
      have hfloor : ((⌊(T : ℚ) * ((M : ℚ) - g)⌋ : ℤ) : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) :=
        Int.floor_le _
      have hcast : (n : ℚ) ≤ (⌊(T : ℚ) * ((M : ℚ) - g)⌋ : ℤ) := by exact_mod_cast hle
      have h_n_le : (n : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := hcast.trans hfloor
      have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
      have h_div : (n : ℚ) / T ≤ (M : ℚ) - g := by
        rw [div_le_iff₀ hT_pos]; linarith
      linarith
  unfold TintPartial
  rw [show (∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) =
      ∑ n ∈ Set.Finite.toFinset (TfiniteBelow p T x g M),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) from
      Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T x g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)))]
  rw [show (∑ n : Set.Finite.toFinset
            (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋),
        (pInvTQ p T) ^ (n.1 : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.1 : ℚ) / T))) =
      ∑ n ∈ Set.Finite.toFinset
          (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) from
      Finset.sum_attach (s := Set.Finite.toFinset
          (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)))]
  rw [hset_eq]

/-- For a null series, the weighted partial sum through integer index `K` has
multiplicative valuation at most `ofAdd (-(K + 1))`. -/
private lemma Tnull_series_tail_bound
    {x : TLiftedPAdicHahnSeries p T} (hx : IsTNullSeries p T x) (g : ℚ) (K : ℤ) :
    Valued.v (TintPartial p T x g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hnhds :
      {y : ℚᶜᵘⁿ_[p,T] | Valued.v y <
          ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
        nhds (0 : ℚᶜᵘⁿ_[p,T]) :=
    Tmem_nhds_zero_v_lt p T WithZero.coe_ne_zero
  have hev_close : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
          (pInvTQ p T) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) <
        ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) : WithZero _) :=
    hx g hnhds
  -- Need ⌊T·(M - g)⌋ ≥ K, i.e., T·(M - g) ≥ K, i.e., M ≥ g + K/T.
  have hev_floor : ∀ᶠ M : ℕ in Filter.atTop, K ≤ ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
    have h_int : ∀ᶠ M : ℕ in Filter.atTop, ⌈g + (K : ℚ) / T⌉₊ ≤ M :=
      Filter.eventually_ge_atTop ⌈g + (K : ℚ) / T⌉₊
    filter_upwards [h_int] with M hM
    have h1 : g + (K : ℚ) / T ≤ (⌈g + (K : ℚ) / T⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((⌈g + (K : ℚ) / T⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    have h3 : g + (K : ℚ) / T ≤ (M : ℚ) := h1.trans h2
    have h4 : (K : ℚ) / T ≤ (M : ℚ) - g := by linarith
    have h5 : (T : ℚ) * ((K : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
      mul_le_mul_of_nonneg_left h4 hT_pos.le
    have hT_eq : (T : ℚ) * ((K : ℚ) / T) = K := by
      rw [mul_div_assoc']; field_simp
    rw [hT_eq] at h5
    exact Int.le_floor.mpr (by exact_mod_cast h5)
  obtain ⟨M, hMle, hMfloor⟩ := (hev_close.and hev_floor).exists
  set K' : ℤ := ⌊(T : ℚ) * ((M : ℚ) - g)⌋ with hK'_def
  have hK'ge : K ≤ K' := hMfloor
  have hpartial_eq := TpartialSum_eq_intPartial p T x g M
  rw [← hK'_def] at hpartial_eq
  rw [hpartial_eq] at hMle
  have hcauchy := Tpartial_sum_valuation_cauchy p T x g K K' hK'ge
  have hsplit : TintPartial p T x g K =
      TintPartial p T x g K' - (TintPartial p T x g K' - TintPartial p T x g K) := by
    ring
  rw [hsplit]
  have h1 : Valued.v (TintPartial p T x g K') ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
    have h_le : ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
      rw [WithZero.coe_le_coe]
      exact Multiplicative.ofAdd_le.mpr (by omega)
    exact le_trans (le_of_lt hMle) h_le
  calc Valued.v (TintPartial p T x g K' - (TintPartial p T x g K' - TintPartial p T x g K))
      ≤ max (Valued.v (TintPartial p T x g K'))
            (Valued.v (TintPartial p T x g K' - TintPartial p T x g K)) :=
        Valuation.map_sub Valued.v _ _
    _ ≤ ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) :=
        max_le h1 hcauchy

/-- Multiplying a null series by an integral Hahn series preserves the partial-sum
bound `ofAdd (-(K + 1))` on each coset. -/
private lemma TintPartial_mul_valuation_bound
    (c x : TLiftedPAdicHahnSeries p T) (hx : IsTNullSeries p T x) (g : ℚ) (K : ℤ) :
    Valued.v (TintPartial p T (c * x) g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  open Pointwise in
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  -- The set of integers `n ≤ K` with `g + n/T ∈ c.support + x.support` is finite.
  have h_sum_pwo : (c.support + x.support).IsPWO := c.isPWO_support.add x.isPWO_support
  have h_outer_ext_finite :
      {n : ℤ | n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support}.Finite := by
    by_cases hs_ne : (c.support + x.support).Nonempty
    · let q_min : ℚ := h_sum_pwo.isWF.min hs_ne
      have hbound : {n : ℤ | n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support} ⊆
          Set.Icc ⌈(T : ℚ) * (q_min - g)⌉ K := by
        intro n hn
        have hge : q_min ≤ g + (n : ℚ) / T := h_sum_pwo.isWF.min_le hs_ne hn.2
        have h1 : q_min - g ≤ (n : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (q_min - g) ≤ (T : ℚ) * ((n : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
          rw [mul_div_assoc']; field_simp
        rw [hT_eq] at h2
        refine ⟨?_, hn.1⟩
        exact Int.ceil_le.mpr (by exact_mod_cast h2)
      exact (Set.finite_Icc _ _).subset hbound
    · have hempty : {n : ℤ | n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support} = ∅ := by
        ext n
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hg
        exact (hs_ne ⟨g + (n : ℚ) / T, hg⟩).elim
      rw [hempty]; exact Set.finite_empty
  let OuterExt : Finset ℤ := h_outer_ext_finite.toFinset
  have hOuterExt_mem : ∀ n : ℤ, n ∈ OuterExt ↔
      n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support := by
    intro n
    exact Set.Finite.mem_toFinset _
  have h_outer_sub : Set.Finite.toFinset (TfiniteBelowInt p T (c * x) g K) ⊆ OuterExt := by
    intro n hn
    have hn_data : n ≤ K ∧ (c * x).coeff (g + (n : ℚ) / T) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T (c * x) g K)).mp hn
    have hcoeff_ne := hn_data.2
    have hsupp : g + (n : ℚ) / T ∈ (c * x).support :=
      (HahnSeries.mem_support _ _).mpr hcoeff_ne
    have hsubset : (c * x).support ⊆ c.support + x.support := HahnSeries.support_mul_subset
    exact (hOuterExt_mem n).mpr ⟨hn_data.1, hsubset hsupp⟩
  have h_intPartial_attach : TintPartial p T (c * x) g K =
      ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T (c * x) g K),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T (c * x) g K))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)))
  have h_extend_eq : TintPartial p T (c * x) g K =
      ∑ n ∈ OuterExt, (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)) := by
    rw [h_intPartial_attach]
    apply Finset.sum_subset h_outer_sub
    intro n hn_outer hn_orig
    have h_ext_data : n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support :=
      (hOuterExt_mem n).mp hn_outer
    have h_ne_orig : ¬ (n ≤ K ∧ (c * x).coeff (g + (n : ℚ) / T) ≠ 0) := by
      intro h
      exact hn_orig
        ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T (c * x) g K)).mpr h)
    have hcx_zero : (c * x).coeff (g + (n : ℚ) / T) = 0 := by
      by_contra hne
      exact h_ne_orig ⟨h_ext_data.1, hne⟩
    rw [hcx_zero, map_zero, mul_zero]
  have h_expand : ∀ n ∈ OuterExt,
      (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)) =
        ∑ ab ∈ Finset.antidiagonal c.isPWO_support x.isPWO_support
            (g + (n : ℚ) / T),
          (pInvTQ p T) ^ n *
            (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff ab.1) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff ab.2)) := by
    intro n _
    rw [HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ab _
    rw [map_mul]
  rw [h_extend_eq, Finset.sum_congr rfl h_expand]
  have h_sigma_eq := Finset.sum_sigma (s := OuterExt)
        (t := fun n => Finset.antidiagonal c.isPWO_support x.isPWO_support
          (g + (n : ℚ) / T))
        (f := fun p_sig : Sigma (fun _ : ℤ => ℚ × ℚ) => (pInvTQ p T) ^ p_sig.1 *
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff p_sig.2.1) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff p_sig.2.2)))
  rw [← h_sigma_eq]
  let Triples : Finset (Sigma (fun _ : ℤ => ℚ × ℚ)) :=
    OuterExt.sigma (fun n => Finset.antidiagonal c.isPWO_support x.isPWO_support
      (g + (n : ℚ) / T))
  let AOf : Finset ℚ := Triples.image (fun s => s.2.1)
  have h_fubini : (∑ p_sig ∈ Triples,
        (pInvTQ p T) ^ p_sig.1 *
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff p_sig.2.1) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff p_sig.2.2))) =
      ∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
        TintPartial p T x (g - a) K := by
    rw [show (∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
          TintPartial p T x (g - a) K) =
        ∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
          ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K),
            (pInvTQ p T) ^ n *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g - a + (n : ℚ) / T)) from by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g - a + (n : ℚ) / T)))]
    rw [show (∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
          ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K),
            (pInvTQ p T) ^ n *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g - a + (n : ℚ) / T))) =
        ∑ a ∈ AOf, ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K),
            (pInvTQ p T) ^ n *
              (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                  (x.coeff (g - a + (n : ℚ) / T))) from by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring]
    have h_sigma_eq2 := Finset.sum_sigma (s := AOf)
      (t := fun a => Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K))
      (f := fun p_sig : Sigma (fun _ : ℚ => ℤ) =>
        (pInvTQ p T) ^ p_sig.2 *
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff p_sig.1) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (x.coeff (g - p_sig.1 + (p_sig.2 : ℚ) / T))))
    rw [← h_sigma_eq2]
    refine Finset.sum_bij
      (fun s _ => ⟨s.2.1, s.1⟩)
      ?_ ?_ ?_ ?_
    · intro s hs
      have hs_data := Finset.mem_sigma.mp hs
      have h_outer_data : s.1 ≤ K ∧ g + (s.1 : ℚ) / T ∈ c.support + x.support :=
        (hOuterExt_mem s.1).mp hs_data.1
      have h_anti_data : s.2.1 ∈ c.support ∧ s.2.2 ∈ x.support ∧
          s.2.1 + s.2.2 = g + (s.1 : ℚ) / T :=
        Finset.mem_antidiagonal.mp hs_data.2
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
      · refine (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x (g - s.2.1) K)).mpr
            ⟨h_outer_data.1, ?_⟩
        have hb_eq : g - s.2.1 + (s.1 : ℚ) / T = s.2.2 := by linarith [h_anti_data.2.2]
        rw [hb_eq]
        exact (HahnSeries.mem_support _ _).mp h_anti_data.2.1
    · intro s₁ hs₁ s₂ hs₂ h_eq
      have hs₁_data := Finset.mem_sigma.mp hs₁
      have hs₂_data := Finset.mem_sigma.mp hs₂
      have h_anti_data₁ := Finset.mem_antidiagonal.mp hs₁_data.2
      have h_anti_data₂ := Finset.mem_antidiagonal.mp hs₂_data.2
      have h_a_eq : s₁.2.1 = s₂.2.1 := (Sigma.mk.inj_iff.mp h_eq).1
      have h_n_eq : s₁.1 = s₂.1 := by
        have h := (Sigma.mk.inj_iff.mp h_eq).2
        exact eq_of_heq h
      have h_b_eq : s₁.2.2 = s₂.2.2 := by
        have h1 : s₁.2.1 + s₁.2.2 = g + (s₁.1 : ℚ) / T := h_anti_data₁.2.2
        have h2 : s₂.2.1 + s₂.2.2 = g + (s₂.1 : ℚ) / T := h_anti_data₂.2.2
        rw [h_a_eq, h_n_eq] at h1
        linarith
      cases s₁ with
      | mk fst snd =>
        cases s₂ with
        | mk fst' snd' =>
          cases snd with
          | mk a b =>
            cases snd' with
            | mk a' b' =>
              simp only at h_a_eq h_n_eq h_b_eq
              subst h_a_eq h_n_eq h_b_eq
              rfl
    · intro t ht
      have ht_data := Finset.mem_sigma.mp ht
      have ht_a_in : t.1 ∈ AOf := ht_data.1
      have ht_n_data : t.2 ≤ K ∧ x.coeff (g - t.1 + (t.2 : ℚ) / T) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x (g - t.1) K)).mp ht_data.2
      obtain ⟨s_orig, hs_orig, hs_eq⟩ := Finset.mem_image.mp ht_a_in
      have hs_orig_data := Finset.mem_sigma.mp hs_orig
      have h_anti_orig := Finset.mem_antidiagonal.mp hs_orig_data.2
      have ha_in_supp : t.1 ∈ c.support := hs_eq ▸ h_anti_orig.1
      let b : ℚ := g - t.1 + (t.2 : ℚ) / T
      have hb_in_supp : b ∈ x.support := (HahnSeries.mem_support _ _).mpr ht_n_data.2
      have hab_sum : t.1 + b = g + (t.2 : ℚ) / T := by simp [b]; ring
      have hn_outer : t.2 ∈ OuterExt := by
        refine (hOuterExt_mem t.2).mpr ⟨ht_n_data.1, ?_⟩
        exact ⟨t.1, ha_in_supp, b, hb_in_supp, hab_sum⟩
      refine ⟨⟨t.2, t.1, b⟩, ?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨hn_outer, ?_⟩
        exact Finset.mem_antidiagonal.mpr ⟨ha_in_supp, hb_in_supp, hab_sum⟩
      · rfl
    · intro s hs
      have hs_data := Finset.mem_sigma.mp hs
      have h_anti_data := Finset.mem_antidiagonal.mp hs_data.2
      have hb_eq : g - s.2.1 + (s.1 : ℚ) / T = s.2.2 := by linarith [h_anti_data.2.2]
      simp only [hb_eq]
  rw [h_fubini]
  apply Valuation.map_sum_le
  intro a _
  rw [Valuation.map_mul]
  have h_alg_le : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a)) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one (c.coeff a)
  have h_inner_le : Valued.v (TintPartial p T x (g - a) K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) :=
    Tnull_series_tail_bound p T hx (g - a) K
  calc Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a)) *
          Valued.v (TintPartial p T x (g - a) K)
      ≤ 1 * Valued.v (TintPartial p T x (g - a) K) := mul_le_mul' h_alg_le (le_refl _)
    _ = Valued.v (TintPartial p T x (g - a) K) := one_mul _
    _ ≤ ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := h_inner_le

/-- T-null-series form an ideal of `TLiftedPAdicHahnSeries p T`. -/
def TNullSeriesIdeal : Ideal (TLiftedPAdicHahnSeries p T) where
  carrier := { x | IsTNullSeries p T x }
  add_mem' := by
    -- Mirrors `NullSeriesIdeal.add_mem'`.
    -- Standard linearity argument: rewrite each partial sum as a sum over the union
    -- of the index sets, then apply `Tendsto.add`.
    intro a b ha hb
    change IsTNullSeries p T a at ha
    change IsTNullSeries p T b at hb
    change IsTNullSeries p T (a + b)
    intro g
    let sa : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (TfiniteBelow p T a g M)
    let sb : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (TfiniteBelow p T b g M)
    let sab : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (TfiniteBelow p T (a + b) g M)
    let su : ℕ → Finset ℤ := fun M => sa M ∪ sb M
    let fa : ℕ → ℤ → ℚᶜᵘⁿ_[p,T] := fun _ n =>
      (pInvTQ p T) ^ n * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (a.coeff (g + (n : ℚ) / T))
    let fb : ℕ → ℤ → ℚᶜᵘⁿ_[p,T] := fun _ n =>
      (pInvTQ p T) ^ n * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (b.coeff (g + (n : ℚ) / T))
    let fab : ℕ → ℤ → ℚᶜᵘⁿ_[p,T] := fun _ n =>
      (pInvTQ p T) ^ n * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((a + b).coeff (g + (n : ℚ) / T))
    have hsab_sub : ∀ M, sab M ⊆ su M := by
      intro M n hn
      have hn' : g + (n : ℚ) / T ≤ M ∧ (a + b).coeff (g + (n : ℚ) / T) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := TfiniteBelow p T (a + b) g M) (a := n)).1 hn
      have hmem : g + (n : ℚ) / T ∈ (a + b).support :=
        (HahnSeries.mem_support (a + b) _).2 hn'.2
      have hunion := HahnSeries.support_add_subset (x := a) (y := b) hmem
      rcases hunion with hxmem | hymem
      · exact Finset.mem_union_left _ <|
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).2 ⟨hn'.1, hxmem⟩
      · exact Finset.mem_union_right _ <|
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).2 ⟨hn'.1, hymem⟩
    have hsuma (M : ℕ) : Finset.sum (su M) (fa M) = Finset.sum (sa M) (fa M) := by
      symm; apply Finset.sum_subset
      · intro n hn; exact Finset.mem_union_left _ hn
      · intro n hnu hnsa
        have hnb : n ∈ sb M := (Finset.mem_union.mp hnu).resolve_left hnsa
        have hmem : g + (n : ℚ) / T ≤ M ∧ b.coeff (g + (n : ℚ) / T) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).1 hnb
        have hxzero : a.coeff (g + (n : ℚ) / T) = 0 := by
          by_contra hxne
          exact hnsa <|
            (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).2 ⟨hmem.1, hxne⟩
        simp [hxzero]
    have hsumb (M : ℕ) : Finset.sum (su M) (fb M) = Finset.sum (sb M) (fb M) := by
      symm; apply Finset.sum_subset
      · intro n hn; exact Finset.mem_union_right _ hn
      · intro n hnu hnsb
        have hna : n ∈ sa M := (Finset.mem_union.mp hnu).resolve_right hnsb
        have hmem : g + (n : ℚ) / T ≤ M ∧ a.coeff (g + (n : ℚ) / T) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).1 hna
        have hyzero : b.coeff (g + (n : ℚ) / T) = 0 := by
          by_contra hyne
          exact hnsb <|
            (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).2 ⟨hmem.1, hyne⟩
        simp [hyzero]
    have hsumab (M : ℕ) : Finset.sum (su M) (fab M) = Finset.sum (sab M) (fab M) := by
      symm; apply Finset.sum_subset
      · exact hsab_sub M
      · intro n hnu hnsab
        have hcoeff : (a + b).coeff (g + (n : ℚ) / T) = 0 := by
          by_contra hne
          exact hnsab <|
            (Set.Finite.mem_toFinset (hs := TfiniteBelow p T (a + b) g M) (a := n)).2 ⟨by
              rcases Finset.mem_union.mp hnu with hna | hnb
              · exact (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).1 hna |>.1
              · exact (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).1 hnb |>.1,
              hne⟩
        simp [hcoeff]
    have hfun :
        (fun M => Finset.sum (sab M) (fab M)) =
          fun M => Finset.sum (sa M) (fa M) + Finset.sum (sb M) (fb M) := by
      funext M
      rw [← hsumab M]
      calc
        Finset.sum (su M) (fab M) = Finset.sum (su M) (fun n => fa M n + fb M n) := by
          apply Finset.sum_congr rfl
          intro n _
          simp [fab, fa, fb, HahnSeries.coeff_add', mul_add, map_add]
        _ = Finset.sum (su M) (fa M) + Finset.sum (su M) (fb M) := by
          rw [Finset.sum_add_distrib]
        _ = Finset.sum (sa M) (fa M) + Finset.sum (sb M) (fb M) := by
          rw [hsuma M, hsumb M]
    have hxmain :
        (fun M => ∑ n : Set.Finite.toFinset (TfiniteBelow p T a g M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (a.coeff (g + (n.val : ℚ) / T))) =
          fun M => Finset.sum (sa M) (fa M) := by
      funext M
      dsimp [sa, fa]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T a g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (a.coeff (g + (n : ℚ) / T))))
    have hymain :
        (fun M => ∑ n : Set.Finite.toFinset (TfiniteBelow p T b g M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (b.coeff (g + (n.val : ℚ) / T))) =
          fun M => Finset.sum (sb M) (fb M) := by
      funext M
      dsimp [sb, fb]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T b g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (b.coeff (g + (n : ℚ) / T))))
    have hmain :
        (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T (a + b) g M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((a + b).coeff (g + (n.val : ℚ) / T))) =
          fun M => Finset.sum (sab M) (fab M) := by
      funext M
      dsimp [sab, fab]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T (a + b) g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((a + b).coeff (g + (n : ℚ) / T))))
    have ha' : Filter.Tendsto (fun M => Finset.sum (sa M) (fa M)) Filter.atTop (nhds 0) := by
      rw [← hxmain]; exact ha g
    have hb' : Filter.Tendsto (fun M => Finset.sum (sb M) (fb M)) Filter.atTop (nhds 0) := by
      rw [← hymain]; exact hb g
    rw [hmain, hfun]
    simpa using ha'.add hb'
  zero_mem' := by
    -- Mirrors `NullSeriesIdeal.zero_mem'`.
    -- The zero series has identically-zero coefficients, so each partial sum is `0`,
    -- and the constant-zero sequence trivially tends to `0`.
    change IsTNullSeries p T 0
    intro g
    simp
  smul_mem' := by
    -- Integer partial sums and the product valuation bound control the null-series tail.
    intro c x hx
    change IsTNullSeries p T (c * x)
    change IsTNullSeries p T x at hx
    intro g
    -- Step 1: rewrite the partial sum as `TintPartial (c*x) g ⌊T·(M - g)⌋`.
    have hpartial_eq : (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T (c * x) g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n.val : ℚ) / T))) =
      fun M : ℕ => TintPartial p T (c * x) g ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
      funext M
      exact TpartialSum_eq_intPartial p T (c * x) g M
    rw [hpartial_eq]
    -- Step 2: setup for ε-style argument via Valued.mem_nhds.
    have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
    have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
      WithZeroMulInt.toNNReal_strictMono hp1
    have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
    have hT_pos : (0 : ℚ) < T := by
      have hT : T ≠ 0 := NeZero.ne T
      exact_mod_cast Nat.pos_of_ne_zero hT
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro U hU
    obtain ⟨γ, hγ_ne, hγ⟩ := Texists_v_lt_subset p T hU
    set ε : NNReal :=
      WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
    have hε_pos : (0 : NNReal) < ε := by
      rw [hε_def]
      exact WithZeroMulInt.toNNReal_pos (p_ne_zero p) hγ_ne
    have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹) ^ N < ε := by
      have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹) ^ n < ε :=
        htendsto.eventually (eventually_lt_nhds hε_pos)
      exact h_eventually.exists
    -- Step 3: pick M₀ so that for M ≥ M₀, ⌊T·(M - g)⌋ + 1 ≥ N.
    rw [Filter.eventually_atTop]
    refine ⟨⌈g + ((N : ℚ) - 1) / T⌉₊, ?_⟩
    intro M hM
    set K : ℤ := ⌊(T : ℚ) * ((M : ℚ) - g)⌋ with hK_def
    have hK_ge : (N : ℤ) - 1 ≤ K := by
      rw [hK_def]
      apply Int.le_floor.mpr
      have h1 : (g + ((N : ℚ) - 1) / T) ≤ (⌈g + ((N : ℚ) - 1) / T⌉₊ : ℚ) := Nat.le_ceil _
      have h2 : ((⌈g + ((N : ℚ) - 1) / T⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
      have h3 : (g + ((N : ℚ) - 1) / T) ≤ (M : ℚ) := h1.trans h2
      have h4 : ((N : ℚ) - 1) / T ≤ (M : ℚ) - g := by linarith
      have h5 : (T : ℚ) * (((N : ℚ) - 1) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
        mul_le_mul_of_nonneg_left h4 hT_pos.le
      have hT_eq : (T : ℚ) * (((N : ℚ) - 1) / T) = (N : ℚ) - 1 := by
        rw [mul_div_assoc']; field_simp
      rw [hT_eq] at h5
      push_cast
      linarith
    have hK_plus_1 : (N : ℤ) ≤ K + 1 := by linarith
    -- Step 4: apply the bound and convert to ε-form.
    apply hγ
    change Valued.v (TintPartial p T (c * x) g K) < γ
    have hbound := TintPartial_mul_valuation_bound p T c x hx g K
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (TintPartial p T (c * x) g K)) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hbound
    have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) =
        (p : NNReal) ^ (-(K + 1)) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero, WithZero.unzero_coe]
      congr 1
    rw [htoNN] at h_nnreal_le
    have h_pow_le : (p : NNReal) ^ (-(K + 1)) ≤ ((p : NNReal)⁻¹) ^ N := by
      rw [show (p : NNReal) ^ (-(K + 1)) = ((p : NNReal)⁻¹) ^ ((K : ℤ) + 1) from by
        rw [zpow_neg, ← inv_zpow]]
      rw [show ((p : NNReal)⁻¹) ^ ((K : ℤ) + 1) = ((p : NNReal)⁻¹) ^ ((K + 1).toNat) from by
        rw [← zpow_natCast]
        congr 1
        omega]
      apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
      omega
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (TintPartial p T (c * x) g K)) < ε :=
      lt_of_le_of_lt (h_nnreal_le.trans h_pow_le) hN
    rw [hε_def] at h_combined
    exact hsm.lt_iff_lt.mp h_combined

private lemma TLifted_partial_sum_split
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) :
    (∑ n : Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((Lifted_to_TLifted p T x).coeff (g + (n.val : ℚ) / T)))
    =
    ∑ r : Fin T, (pInvTQ p T) ^ (r.val : ℕ) *
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (∑ m : Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M),
            ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (m.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p])
                (x.coeff ((g + (r.val : ℚ) / T) + (m.val : ℚ)))) := by
  classical
  have hT_ne : (T : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne T
  have hT_pos : (0 : ℤ) < T := by exact_mod_cast Nat.pos_of_neZero T
  have hT_pos_q : (0 : ℚ) < T := by exact_mod_cast Nat.pos_of_neZero T
  have hpInvTQ_ne : (pInvTQ p T) ≠ 0 := pInvTQ_ne_zero p T
  -- Convert sums-over-attach to sums-over-finset.
  rw [Finset.univ_eq_attach, Finset.sum_attach
    (Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M))
    (fun n => (pInvTQ p T) ^ (n : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((Lifted_to_TLifted p T x).coeff (g + (n : ℚ) / T)))]
  -- Push algebraMap and reindex on RHS to a doubled sum on K side.
  have h_RHS : ∀ r : Fin T,
      (pInvTQ p T) ^ (r.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
          (∑ m : Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M),
            ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (m.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p])
                (x.coeff ((g + (r.val : ℚ) / T) + (m.val : ℚ)))) =
      ∑ m ∈ Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M),
        (pInvTQ p T) ^ ((T : ℤ) * (m : ℤ) + (r.val : ℤ)) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((Lifted_to_TLifted p T x).coeff
              (g + (((T : ℤ) * (m : ℤ) + (r.val : ℤ) : ℤ) : ℚ) / T)) := by
    intro r
    rw [Finset.univ_eq_attach, Finset.sum_attach
      (Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M))
      (fun m => ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (m : ℤ) *
        algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ))))]
    rw [map_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    -- Single-term identity:
    -- pInvTQ^r * algMap (p^m * algMap (x.coeff h)) where h = g + r/T + m
    -- = pInvTQ^(T*m+r) * algMap_{R→K}(OQpCUn_embd (x.coeff h))
    -- = pInvTQ^(T*m+r) * algMap_{R→K}((ι x).coeff (g + (T*m+r)/T))
    rw [map_mul, map_zpow₀]
    -- p in K₀ as algMap from R₀
    have hp_K0 : ((p : ℕ) : ℚᶜᵘⁿ_[p]) =
        algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p]) := by simp
    -- algMap_{K₀→K} (algMap_{R₀→K₀} z) = algMap_{R→K} (OQpCUn_embd z)
    have h_compat : algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ)))) =
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (OQpCUn_embd p T (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ)))) :=
      (algebraMap_OQpCUn_embd_compat p T _).symm
    rw [h_compat]
    -- Compute index identity g + (T*m+r)/T = (g + r/T) + m
    have h_idx : g + (((T : ℤ) * (m : ℤ) + (r.val : ℤ) : ℤ) : ℚ) / T =
        (g + (r.val : ℚ) / T) + (m : ℚ) := by
      push_cast; field_simp; ring
    rw [show (Lifted_to_TLifted p T x).coeff
        (g + (((T : ℤ) * (m : ℤ) + (r.val : ℤ) : ℤ) : ℚ) / T) =
        OQpCUn_embd p T (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ))) from by
      rw [h_idx]; rfl]
    -- Now compute pInvTQ^r * algMap p^m * algMap_{R→K}(...)
    -- = pInvTQ^r * pInvTQ^(T*m) * algMap_{R→K}(...)
    have h_alg_p_pow : (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])))^(m : ℤ) =
        (pInvTQ p T) ^ ((T : ℤ) * (m : ℤ)) := by
      rw [← hp_K0, ← map_zpow₀, ← pInvTQ_pow_T_zmul]
    rw [hp_K0]
    rw [h_alg_p_pow]
    -- Combine: pInvTQ^r * pInvTQ^(T*m) = pInvTQ^(T*m + r)
    rw [← mul_assoc]
    rw [show ((pInvTQ p T) ^ (r.val : ℕ)) = ((pInvTQ p T) ^ ((r.val : ℤ))) by rfl]
    rw [show ((pInvTQ p T) ^ ((r.val : ℤ)) * (pInvTQ p T) ^ ((T : ℤ) * (m : ℤ))) =
        (pInvTQ p T) ^ (((T : ℤ) * (m : ℤ)) + (r.val : ℤ)) from by
      rw [← zpow_add₀ hpInvTQ_ne]; congr 1; ring]
  simp_rw [h_RHS]
  -- Now both sides are sums of the same kind of terms, indexed differently.
  -- Apply Finset.sum_sigma to combine the RHS into a sum over a sigma type,
  -- then use Finset.sum_bij with the bijection n ↔ (r, m) where n = T*m + r.val.
  rw [← Finset.sum_sigma Finset.univ
      (fun r : Fin T => Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M))
      (fun rm : Σ _ : Fin T, ℤ =>
        (pInvTQ p T) ^ ((T : ℤ) * rm.2 + (rm.1.val : ℤ)) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((Lifted_to_TLifted p T x).coeff
              (g + (((T : ℤ) * rm.2 + (rm.1.val : ℤ) : ℤ) : ℚ) / T)))]
  -- Apply Finset.sum_bij with the bijection n ↔ ⟨n % T, n / T⟩.
  classical
  have hT_natpos : (0 : ℕ) < T := Nat.pos_of_neZero T
  refine Finset.sum_bij
      (fun n (_ : n ∈ Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M)) =>
        (⟨⟨(n.emod (T : ℤ)).toNat, ?_⟩, n.ediv (T : ℤ)⟩ : Σ _ : Fin T, ℤ)) ?_ ?_ ?_ ?_
  · -- (n.emod T).toNat < T
    have hmod_nn : 0 ≤ n.emod (T : ℤ) := Int.emod_nonneg n hT_ne
    have hmod_lt : n.emod (T : ℤ) < (T : ℤ) := Int.emod_lt_of_pos n hT_pos
    omega
  · -- membership: ⟨n%T, n/T⟩ ∈ univ.sigma (...)
    intro n hn
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
    rw [Set.Finite.mem_toFinset] at hn ⊢
    have hmod_nn : 0 ≤ n.emod (T : ℤ) := Int.emod_nonneg n hT_ne
    have hmod_lt : n.emod (T : ℤ) < (T : ℤ) := Int.emod_lt_of_pos n hT_pos
    have htoNat : ((n.emod (T : ℤ)).toNat : ℤ) = n.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn
    have hsplit_int : (T : ℤ) * n.ediv (T : ℤ) + n.emod (T : ℤ) = n := Int.mul_ediv_add_emod n T
    have hn_split : ((n : ℚ) / T) =
        (((n.emod (T : ℤ)).toNat : ℚ) / T + (n.ediv (T : ℤ) : ℚ)) := by
      have hQ : (n : ℚ) =
          ((T : ℤ) * n.ediv (T : ℤ) + n.emod (T : ℤ) : ℤ) := by exact_mod_cast hsplit_int.symm
      rw [hQ]; push_cast
      have hcast : ((n.emod (T : ℤ) : ℤ) : ℚ) = ((n.emod (T : ℤ)).toNat : ℚ) := by
        have := htoNat
        exact_mod_cast this.symm
      rw [hcast]
      field_simp; ring
    have hcoeff_eq : (Lifted_to_TLifted p T x).coeff (g + (n : ℚ) / T) = OQpCUn_embd p T
      (x.coeff (g + ((n.emod (T : ℤ)).toNat : ℚ) / T + (n.ediv (T : ℤ) : ℚ))) := by
      rw [show g + (n : ℚ) / T =
          g + ((n.emod (T : ℤ)).toNat : ℚ) / T + (n.ediv (T : ℤ) : ℚ) from by
        rw [hn_split]; ring]
      rfl
    refine ⟨?_, ?_⟩
    · have h1 := hn.1
      rw [hn_split] at h1; linarith
    · intro h0
      apply hn.2
      rw [hcoeff_eq, h0, map_zero]
  · -- injectivity
    intro n₁ hn₁ n₂ hn₂ hij
    simp only [Sigma.mk.injEq, Fin.mk.injEq, heq_eq_eq] at hij
    obtain ⟨hmod, hdiv⟩ := hij
    have hmod_nn₁ : 0 ≤ n₁.emod (T : ℤ) := Int.emod_nonneg n₁ hT_ne
    have hmod_nn₂ : 0 ≤ n₂.emod (T : ℤ) := Int.emod_nonneg n₂ hT_ne
    have h_emod : n₁.emod (T : ℤ) = n₂.emod (T : ℤ) := by
      have h1 : ((n₁.emod (T : ℤ)).toNat : ℤ) = n₁.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn₁
      have h2 : ((n₂.emod (T : ℤ)).toNat : ℤ) = n₂.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn₂
      have hcast : ((n₁.emod (T : ℤ)).toNat : ℤ) = ((n₂.emod (T : ℤ)).toNat : ℤ) := by
        exact_mod_cast hmod
      rw [h1, h2] at hcast; exact hcast
    have h_split₁ : (T : ℤ) * n₁.ediv (T : ℤ) + n₁.emod (T : ℤ) = n₁ := Int.mul_ediv_add_emod _ _
    have h_split₂ : (T : ℤ) * n₂.ediv (T : ℤ) + n₂.emod (T : ℤ) = n₂ := Int.mul_ediv_add_emod _ _
    rw [← h_split₁, ← h_split₂, hdiv, h_emod]
  · -- surjectivity
    rintro ⟨r, m⟩ hrm
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hrm
    rw [Set.Finite.mem_toFinset] at hrm
    refine ⟨(T : ℤ) * m + (r.val : ℤ), ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      have hidx : g + (((T : ℤ) * m + (r.val : ℤ) : ℤ) : ℚ) / T =
          g + (r.val : ℚ) / T + (m : ℚ) := by
        push_cast; field_simp; ring
      refine ⟨?_, ?_⟩
      · rw [hidx]; exact hrm.1
      · rw [hidx]
        intro h0
        apply hrm.2
        have h1 : OQpCUn_embd p T (x.coeff (g + (r.val : ℚ) / T + (m : ℚ))) = 0 := h0
        have : OQpCUn_embd p T (x.coeff (g + (r.val : ℚ) / T + (m : ℚ))) =
          OQpCUn_embd p T 0 := by rw [h1, map_zero]
        exact (OQpCUn_embd_injective p T) this
    · -- bijection function value matches
      have hr_lt : (r.val : ℤ) < T := by exact_mod_cast r.isLt
      have hr_nn : (0 : ℤ) ≤ r.val := Int.natCast_nonneg _
      have h_emod : ((T : ℤ) * m + (r.val : ℤ)).emod (T : ℤ) = (r.val : ℤ) := by
        have : ((T : ℤ) * m + (r.val : ℤ)) % (T : ℤ) = (r.val : ℤ) := by
          have heq : (T : ℤ) * m + (r.val : ℤ) = (r.val : ℤ) + m * (T : ℤ) := by ring
          rw [heq, Int.add_mul_emod_self_right]
          exact Int.emod_eq_of_lt hr_nn hr_lt
        exact this
      have h_ediv : ((T : ℤ) * m + (r.val : ℤ)).ediv (T : ℤ) = m := by
        have : ((T : ℤ) * m + (r.val : ℤ)) / (T : ℤ) = m := by
          have heq : (T : ℤ) * m + (r.val : ℤ) = (r.val : ℤ) + m * (T : ℤ) := by ring
          rw [heq, Int.add_mul_ediv_right _ _ hT_ne]
          rw [show (r.val : ℤ) / (T : ℤ) = 0 from Int.ediv_eq_zero_of_lt hr_nn hr_lt, zero_add]
        exact this
      apply Sigma.ext
      · simp only [h_emod]
        apply Fin.ext
        simp only
        exact_mod_cast Int.toNat_of_nonneg hr_nn
      · simp only [h_ediv, heq_eq_eq]
  · -- function values agree
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    have hT_ne_q : (T : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne T
    have hmod_nn : 0 ≤ n.emod (T : ℤ) := Int.emod_nonneg n hT_ne
    have htoNat : ((n.emod (T : ℤ)).toNat : ℤ) = n.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn
    have hsplit_int : (T : ℤ) * n.ediv (T : ℤ) + ((n.emod (T : ℤ)).toNat : ℤ) = n := by
      rw [htoNat]; exact Int.mul_ediv_add_emod n T
    have h_idx_eq :
        (g + ((((n.emod (T : ℤ)).toNat : ℤ) : ℚ) / T + (n.ediv (T : ℤ) : ℚ))) =
        (g + (n : ℚ) / T) := by
      have hQ : (n : ℚ) = ((T : ℤ) * n.ediv (T : ℤ) + ((n.emod (T : ℤ)).toNat : ℤ) : ℤ) := by
        exact_mod_cast hsplit_int.symm
      rw [hQ]; push_cast; field_simp; ring
    -- Show: pInvTQ^(T*(n/T) + (n%T).toNat) * algMap ((ι x).coeff (g + (T*(n/T) + (n%T).toNat)/T))
    --     = pInvTQ^n * algMap ((ι x).coeff (g + n/T))
    have h_exp_eq : (T : ℤ) * n.ediv (T : ℤ) + ((n.emod (T : ℤ)).toNat : ℤ) = n := hsplit_int
    rw [h_exp_eq]

/-- The weighted partial sum on an integer coset in the unramified coefficient field. -/
private noncomputable def S_partial
    (x : LiftedPAdicHahnSeries p) (h : ℚ) (M : ℕ) : ℚᶜᵘⁿ_[p] :=
  ∑ n : Set.Finite.toFinset (finiteBelow x h M),
    ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (n.val : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (x.coeff (h + n.val))

/-- The weighted partial sum on a coset of `(1/T)ℤ` after extending coefficients
to the ramified ring. -/
private noncomputable def T_partial
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) : ℚᶜᵘⁿ_[p,T] :=
  ∑ n : Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M),
    (pInvTQ p T) ^ (n.val : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((Lifted_to_TLifted p T x).coeff (g + (n.val : ℚ) / T))

/-- Splitting the integer index into residue classes modulo `T` expresses the
ramified partial sum through the power-basis projections of unramified partial sums. -/
private lemma T_partial_eq_proj_sum
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) :
    T_partial p T x g M
      = ∑ r : Fin T, (pInvTQ p T) ^ (r.val : ℕ) *
          algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
            (S_partial p x (g + (r.val : ℚ) / T) M) := by
  unfold T_partial S_partial
  exact TLifted_partial_sum_split (p := p) (T := T) x g M

open Topology Filter in
private lemma tendsto_T_partial_of_null
    (x : LiftedPAdicHahnSeries p)
    (hN : ∀ h, Filter.Tendsto (fun M => S_partial p x h M) Filter.atTop (𝓝 0))
    (g : ℚ) :
    Filter.Tendsto (fun M => T_partial p T x g M) Filter.atTop (𝓝 0) := by
  have hf : (fun M => T_partial p T x g M) =
      (fun M => ∑ r : Fin T, (pInvTQ p T) ^ (r.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
          (S_partial p x (g + (r.val : ℚ) / T) M)) := by
    funext M; exact T_partial_eq_proj_sum p T x g M
  rw [hf]
  have hzero : (0 : ℚᶜᵘⁿ_[p,T]) = ∑ _r : Fin T, (0 : ℚᶜᵘⁿ_[p,T]) := by simp
  rw [hzero]
  refine tendsto_finsetSum _ ?_
  intro r _
  -- For each r: π^r · ι̃(S_partial p x (g + r/T) M) → π^r · 0 = 0.
  have h_inner : Filter.Tendsto
      (fun M => algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (S_partial p x (g + (r.val : ℚ) / T) M))
      Filter.atTop (𝓝 0) := by
    have hcts := (continuous_algebraMap_K₀_K p T).tendsto 0
    have h0 : (0 : ℚᶜᵘⁿ_[p,T])
        = algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) 0 := (map_zero _).symm
    rw [h0]
    exact hcts.comp (hN (g + (r.val : ℚ) / T))
  have h_mul := h_inner.const_mul ((pInvTQ p T) ^ (r.val : ℕ))
  simpa using h_mul

open Topology Filter in
private lemma tendsto_S_partial_of_T_null
    (x : LiftedPAdicHahnSeries p)
    (hT : ∀ g, Filter.Tendsto (fun M => T_partial p T x g M) Filter.atTop (𝓝 0))
    (h : ℚ) :
    Filter.Tendsto (fun M => S_partial p x h M) Filter.atTop (𝓝 0) := by
  -- Apply continuous_QpCUn_proj 0 to hT h.
  have h_proj : Filter.Tendsto
      (fun M => QpCUn_proj p T 0 (T_partial p T x h M)) Filter.atTop (𝓝 0) := by
    have hcts := (continuous_QpCUn_proj p T 0).tendsto 0
    have h0 : (0 : ℚᶜᵘⁿ_[p]) = QpCUn_proj p T 0 0 := by
      rw [map_zero]
    rw [h0]
    exact hcts.comp (hT h)
  -- Show the projection equals S_partial pointwise.
  have h_eq : ∀ M, QpCUn_proj p T 0 (T_partial p T x h M) = S_partial p x h M := by
    intro M
    rw [T_partial_eq_proj_sum]
    rw [QpCUn_proj_sum (p := p) (T := T)
        (a := fun r : Fin T => S_partial p x (h + (r.val : ℚ) / T) M) 0]
    show S_partial p x (h + ((0 : Fin T).val : ℚ) / T) M = S_partial p x h M
    have hzero : ((0 : Fin T).val : ℚ) = 0 := by simp
    rw [hzero]
    simp
  exact h_proj.congr h_eq

open Topology Filter in
/-- Extending coefficients to the ramified ring preserves and reflects the
null-series condition. Equivalently, the preimage of the ramified null-series ideal under
the coefficient inclusion is the original null-series ideal. This replaces the summation of
the identities for the residues `0 ≤ j < T` in the proof of Proposition 3.4. -/
theorem TNullSeriesIdeal_inter_image :
    ∀ x : LiftedPAdicHahnSeries p,
      Lifted_to_TLifted p T x ∈ TNullSeriesIdeal p T ↔ x ∈ NullSeriesIdeal p := by
  intro x
  change IsTNullSeries p T (Lifted_to_TLifted p T x) ↔ IsNullSeries x
  change (∀ g, Filter.Tendsto (fun M => T_partial p T x g M) Filter.atTop (𝓝 0))
      ↔ (∀ h, Filter.Tendsto (fun M => S_partial p x h M) Filter.atTop (𝓝 0))
  refine ⟨fun hT h => ?_, fun hN g => ?_⟩
  · exact tendsto_S_partial_of_T_null (p := p) (T := T) x hT h
  · exact tendsto_T_partial_of_null (p := p) (T := T) x hN g

end RamifiedCoefficients

end PAdicOrderType
