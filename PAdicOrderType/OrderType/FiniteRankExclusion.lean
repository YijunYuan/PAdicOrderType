/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateHomogeneity
import PAdicOrderType.Coefficients.CarryFreeFiber
import PAdicOrderType.Digits.SeparatedPlacements
import PAdicOrderType.OrderType.Reduction
import PAdicOrderType.Digits.TailRep
import PAdicOrderType.Coefficients.SeparatedCoefficient
import PAdicOrderType.Coefficients.TruncationIdentity
import PAdicOrderType.Coefficients.ValuationFacts
import PAdicOrderType.Digits.QTR
import TrustworthyKedlaya.MainResults

/-!
# Finite-rank exclusion for algebraic p-adic Hahn series

This file proves Theorem 4.1: an algebraic p-adic Hahn series with support order type below
`ω ^ ω` has order type at most `ω`. A positive essential rank would give an upper bound on
polynomial values at all sufficiently large truncations (Proposition 3.1), contradicting an
annihilating polynomial.

## Main statements

* `PAdicOrderType.exists_local_qtr`: each integer closed truncation of an algebraic series
  has quasi-twist-recurrent coefficients, with data that may depend on the cutoff
  (Corollary 2.10).
* `PAdicOrderType.uniform_polynomial_bound`: the additive valuation of `P(g)` is at most
  `n * (R₀ + 1) + kC + ka`, independently of the upper support cutoff and recurrence data
  (Proposition 3.1).
* `PAdicOrderType.finite_rank_exclusion_core`: a polynomial relation contradicts the bound
  when a positive truncation rank is attained and no higher rank is attained (the
  contradiction in the proof of Theorem 4.1).
* `PAdicOrderType.typeLT_support_le_omega0_of_lt_omega0_pow_omega0`: the resulting
  support bound for every algebraic series of order type below `ω ^ ω` (Theorem 4.1).

## Implementation notes

Proposition 3.1 is stated for monic polynomials over `ℤ_p`. The uniform estimate here allows
polynomials over the unramified coefficient ring with a nonunit leading coefficient; `ka`
records its additive valuation. The constant `kC` is the p-adic valuation of
`PAdicOrderType.interleavingConstant n r` and plays the role of the constant `C(n, r)` of
Lemma 3.15. Multiplication by a power of `p` reduces general supports to the nonnegative case
without changing their order type, as in the proof of Theorem 4.1.
-/

-- `HahnSeries.powerSeriesAlgebra` (imported through `PAdicOrderType.Digits.DigitEncoding`) would be
-- selected as the `ℤᶜᵘⁿ_[p]`-algebra structure of `LiftedPAdicHahnSeries p` and hence of `𝕃_[p]`,
-- breaking unification with the scalar-tower instance of `TrustworthyKedlaya`; we remove it
-- locally.
attribute [-instance] HahnSeries.powerSeriesAlgebra

namespace PAdicOrderType

open DigitSeries RamifiedCoefficients CoefficientCosets TrustworthyKedlaya
  TrustworthyKedlaya.pAdicHahnSeries Ordinal LaurentSeries Multiplicity

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Corollary 2.10: the coefficients of every integer closed truncation of a
`ℚ_[p]`-algebraic p-adic Hahn series are quasi-twist recurrent. The data `(a, b, c, M, N)` may
depend on the series and the cutoff. -/
theorem exists_local_qtr (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f) (R : ℤ) :
    ∃ (a : ℕ+) (b c : ℕ) (M N : ℕ+),
      IsQTR (fun q => if q ≤ (R : ℚ) then f.coeff q else 0) a b c M N := by
  classical
  -- Integral elements are truncationwise UP; cut just above the closed endpoint.
  let g' := trunc ((R + 1 : ℤ) : ℚ) f
  have hg' : UP.IsUP p g' :=
    (isTruncUP_of_isIntegral_QpCUn (alg_QpCUn_of_alg_Qp p f hf).isIntegral).trunc_intCast (R + 1)
  obtain ⟨a, b, c, M, N, hw⟩ := UP.isUP_iff_exists_sliceWitness.mp hg'
  have hqtr : IsQTR g'.coeff a b c M N :=
    ⟨g'.isWF_support, hw.1,
      QTR.recurrence_of_twist g' a b c M N fun m hm => hw.2 m hm⟩
  refine ⟨a, b, c, M, N, ?_⟩
  -- restrict to `(-∞, R]` (`isQTR_restrict`) and identify the truncation with that of `f`
  have hrestr := isQTR_restrict hqtr R
  have hfeq : (fun q => if q ≤ (R : ℚ) then f.coeff q else 0)
      = fun q => if q ≤ (R : ℚ) then g'.coeff q else 0 := by
    funext q
    by_cases hq : q ≤ (R : ℚ)
    · rw [if_pos hq, if_pos hq]
      exact (coeff_trunc_of_lt (by push_cast; linarith : q < ((R + 1 : ℤ) : ℚ)) f).symm
    · rw [if_neg hq, if_neg hq]
  rw [hfeq]
  exact hrestr

/-- A QTR support bounded above by an integer `R` lies in the slices `S_{a,b,c,m}` with
`-b ≤ m ≤ a R`. Thus only finitely many integer parts `m` occur, as used in the proof of
Lemma 3.6. -/
theorem support_subset_slices_of_le {f : 𝕃_[p]} {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    (hqtr : IsQTR f.coeff a b c M N) {R : ℤ} (hR : ∀ q ∈ f.support, q ≤ (R : ℚ)) :
    f.support ⊆ ⋃ m ∈ Set.Icc (-(b : ℤ)) ((a : ℤ) * R), Sabc_m p a c m := by
  intro q hq
  obtain ⟨m, d, hmb, hdp, hdc, hqeq⟩ := hqtr.2.1 hq
  have hval := digitVal_mem_Ico (p := p) hdp
  refine Set.mem_biUnion (Set.mem_Icc.mpr ⟨hmb, ?_⟩) ⟨d, hdp, hdc, hqeq⟩
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have hqR := hR q hq
  rw [hqeq] at hqR
  have h1 : (m : ℚ) - d.sum (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ≤ (a : ℚ) * R := by
    have := mul_le_mul_of_nonneg_left hqR ha.le
    rwa [← mul_assoc, mul_one_div_cancel ha.ne', one_mul] at this
  have h2 : (m : ℚ) < (a : ℚ) * R + 1 := by linarith [hval.2]
  have h3 : (m : ℚ) < (((a : ℤ) * R + 1 : ℤ) : ℚ) := by push_cast; exact h2
  have h4 : m < (a : ℤ) * R + 1 := by exact_mod_cast h3
  omega

/-- The multiset attached to a multiplicity function has `|φ|` elements. -/
lemma card_toMultiset_eq_card (φ : DigitSeries →₀ ℕ) :
    Multiset.card φ.toMultiset = card φ := by
  rw [Finsupp.card_toMultiset]; rfl

/-- The multiset attached to a multiplicity function sums to `Σ(φ)`. -/
lemma sum_toMultiset_eq_total (φ : DigitSeries →₀ ℕ) : φ.toMultiset.sum = total φ := by
  classical
  have h1 : φ.toMultiset.sum = (φ.toMultiset.map id).sum := by rw [Multiset.map_id]
  rw [h1, Finset.sum_multiset_map_count, Finsupp.toFinset_toMultiset, total_eq_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finsupp.count_toMultiset]
  rfl

/-- Raising `ofAdd (-m)` to the natural power `n` multiplies its additive exponent
by `n`. -/
lemma coe_ofAdd_neg_pow (m : ℤ) (n : ℕ) :
    ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ n =
      ((Multiplicative.ofAdd (-((n : ℤ) * m)) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← WithZero.coe_mul, ← ofAdd_add]
    congr 2
    push_cast
    ring

/-- **Uniform polynomial bound** (Proposition 3.1): let `g` have bounded QTR support of
order type below `ω ^ (r + 1)`, with a closed truncation at `R₀` of order type at least
`ω ^ r`, where `r > 0`, as in Assumption 3.10. For a degree-`n` polynomial `P` over the
unramified integral coefficient ring, with `n > 0`, the additive valuation of `P(g)` is at most
`n * (R₀ + 1) + kC + ka`.

Here `ka` is the additive valuation of the leading coefficient, and `kC` is that of
`PAdicOrderType.interleavingConstant n r`, expressed through the normalized multiplicative
valuations of the ramified fields. The bound is independent of the QTR data and the upper
support cutoff. For a monic polynomial, `ka = 0`, and the bound is inequality (3.1) with
`C(n, r) = kC`. As in the proof of Proposition 3.1, Lemma 3.16 supplies a rigid digit vector,
and Proposition 3.4 converts its coefficient into the bound. -/
theorem uniform_polynomial_bound (g : 𝕃_[p])
    {a : ℕ+} {b c : ℕ} {M N : ℕ+} (hqtr : IsQTR g.coeff a b c M N)
    {R : ℤ} (hgR : ∀ q ∈ g.support, q ≤ (R : ℚ))
    (P : Polynomial ℤᶜᵘⁿ_[p]) {n : ℕ} (hn : 0 < n) (hdeg : P.natDegree = n)
    {r : ℕ} (hr : 0 < r) {R₀ : ℤ}
    (hU : omega0 ^ r ≤ typeLT ↥(g.support ∩ Set.Iic (R₀ : ℚ)))
    (hV : typeLT g.support < omega0 ^ (r + 1))
    {ka kC : ℕ}
    (hka : ∀ T : ℕ+,
      Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
        (OQpCUn_embd p T (P.coeff n))) =
      ((Multiplicative.ofAdd (-((T : ℤ) * ka)) : Multiplicative ℤ) : WithZero _))
    (hkC : ∀ T : ℕ+, Valued.v (interleavingConstant n r : ℚᶜᵘⁿ_[p,(T : ℕ)]) =
      ((Multiplicative.ofAdd (-((T : ℤ) * kC)) : Multiplicative ℤ) : WithZero _)) :
    val p (Polynomial.aeval g P) ≤
      ((((n : ℤ) * (R₀ + 1) + kC + ka : ℤ) : ℚ) : WithTop ℚ) := by
  classical
  set U₀ : ℤ := R₀ + 1 with hU₀
  set V₀ : ℤ := (n : ℤ) * U₀ + kC + ka with hV₀
  change val p (Polynomial.aeval g P) ≤ ((V₀ : ℚ) : WithTop ℚ)
  by_contra hle
  have hval : ((V₀ : ℚ) : WithTop ℚ) < val p (Polynomial.aeval g P) := lt_of_not_ge hle
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hsub := support_subset_slices_of_le hqtr hgR
  have hwf : WellFoundedLT ↥(Function.support g.coeff) :=
    inferInstanceAs (WellFoundedLT ↥g.support)
  -- ### the ray-marker lemma
  obtain ⟨h₀, hmarker⟩ := exists_ray_marker hqtr le_rfl hsub hr hV hU n
  obtain ⟨μ, hH, hgeometry, hclust, α, hα0, hαp, hplace⟩ := hmarker h₀ le_rfl
  -- ### `T = a p^h₀` and the representatives `D` of `-T·Supp(g)`
  set T : ℕ+ := a * ⟨p ^ h₀, pow_pos hp_pos h₀⟩ with hTdef
  have hT : (T : ℕ) = (a : ℕ) * p ^ h₀ := rfl
  have hTpos : (0 : ℤ) < (T : ℤ) := by exact_mod_cast T.pos
  obtain ⟨hD, hf2, htail_mem, hD_eq_tail⟩ := tail_rep_data g hsub hT
  set D : Set DigitSeries :=
    {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ g.support} with hDdef
  -- QTR insertions preserve every integer-indexed coefficient in a digit coset.
  -- Thus its aggregate depends only on the ordered block patterns.
  obtain ⟨lo, Δ, hs, hlo, hΔ, hdiv, hB⟩ := hgeometry
  have hhom := exists_aggregate_homogeneity hf2 hqtr hT hs hlo hΔ hdiv hB r
  -- ### every representative occupies at most `r` core blocks
  have hblocks : ∀ d ∈ D, (∀ i : ℕ+, d i ≠ 0 → ∃ j, i ∈ μ.b j) →
      ∀ J : Finset ℕ, (∀ j ∈ J, ∃ i ∈ μ.b j, d i ≠ 0) → J.card ≤ r := by
    intro d hd _ J hJ
    obtain ⟨m, dv, hdig, hq, hdeq⟩ := hD_eq_tail d hd
    obtain ⟨cl, hclcard, hcover, hclI⟩ := hclust m dv hdig hq
    rw [← hdeq] at hcover
    choose i hiB hdi using hJ
    have hC : ∀ j (hj : j ∈ J), ∃ C ∈ cl, i j hj ∈ C := fun j hj => hcover _ (hdi j hj)
    choose C hCcl hiC using hC
    let Φ : ℕ → Finset ℕ+ := fun j => if hj : j ∈ J then C j hj else ∅
    have hΦ : ∀ j (hj : j ∈ J), Φ j = C j hj := fun j hj => dif_pos hj
    have hCBt : ∀ j (hj : j ∈ J), C j hj ⊆ μ.bt j := fun j hj =>
      hclI _ (hCcl j hj) j ⟨i j hj, Finset.mem_inter.mpr ⟨hiC j hj, μ.b_subset_i j (hiB j hj)⟩⟩
    refine le_trans (Finset.card_le_card_of_injOn Φ ?_ ?_) hclcard
    · intro j hj
      rw [hΦ j hj]
      exact hCcl j hj
    · intro j hj j' hj' hjj'
      simp only [Finset.mem_coe] at hj hj'
      rw [hΦ j hj, hΦ j' hj'] at hjj'
      by_contra hne
      have hdisj := μ.bt_disjoint hne
      have h1 : i j hj ∈ μ.bt j := hCBt j hj (hiC j hj)
      have h2 : i j hj ∈ μ.bt j' := hCBt j' hj' (hjj' ▸ hiC j hj)
      exact Finset.disjoint_left.mp hdisj h1 h2
  -- ### the marker placements lie in `D` with valuation `≥ ofAdd (-(T U₀))`
  set γ₀ : WithZero (Multiplicative ℤ) :=
    ((Multiplicative.ofAdd (-((T : ℤ) * U₀)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with hγ₀
  have hγ₀0 : γ₀ ≠ 0 := WithZero.coe_ne_zero
  have hplace' : ∀ jj : Fin r → ℕ, StrictMono jj →
      (∑ i, placeAt (μ.b (jj i)) (α i)) ∈ D ∧
        γ₀ ≤ Valued.v (adFun hf2 ((∑ i, placeAt (μ.b (jj i)) (α i)))) := by
    intro jj hjj
    obtain ⟨m, dv, hdig, hq, hqR₀, htail⟩ := hplace jj hjj
    have hmem : tailh (ofFinsupp dv) h₀ ∈ D := htail_mem m dv hdig hq
    rw [← htail]
    refine ⟨hmem, ?_⟩
    rw [adFun_apply_of_mem hf2 hmem]
    unfold ad
    rw [Valuation.map_mul, valued_v_pInvT_zpow, valued_cs_eq_one, mul_one, hγ₀,
      WithZero.coe_le_coe, Multiplicative.ofAdd_le, neg_le_neg_iff]
    -- `aggExp = ‖d‖ + T s_d ≤ T U₀` since `s_d ≤ q ≤ R₀` and `‖d‖ < 1`
    have hcast := aggExp_cast hf2 ⟨tailh (ofFinsupp dv) h₀, hmem⟩
    have hnorm := DigitSeries.norm_mem_Ico p _ (hD _ hmem)
    have hkey := mul_qval_eq_sub_norm_tailh hT m dv
    have hq_Sd : qval p a m dv ∈ Sd p g T (tailh (ofFinsupp dv) h₀) := by
      refine ⟨hq, ?_⟩
      change (((tailh (ofFinsupp dv) h₀).norm p : ℚ) + (T : ℚ) * qval p a m dv).isInt = true
      rw [hkey, show ((tailh (ofFinsupp dv) h₀).norm p : ℚ) +
          ((((p : ℤ) ^ h₀ * m - (pih p (ofFinsupp dv) h₀ : ℤ) : ℤ) : ℚ) -
            (tailh (ofFinsupp dv) h₀).norm p) =
          ((((p : ℤ) ^ h₀ * m - (pih p (ofFinsupp dv) h₀ : ℤ) : ℤ) : ℚ)) by ring]
      exact isInt_intCast' _
    have hmu_le : muQ hf2 ⟨tailh (ofFinsupp dv) h₀, hmem⟩ ≤ qval p a m dv :=
      (Sd_isWF g T _).min_le _ hq_Sd
    have hTU : (T : ℚ) * (R₀ : ℚ) + 1 ≤ (T : ℚ) * (U₀ : ℚ) := by
      rw [hU₀]; push_cast
      have : (1 : ℚ) ≤ (T : ℚ) := by exact_mod_cast T.pos
      nlinarith
    have hlt : ((aggExp hf2 ⟨tailh (ofFinsupp dv) h₀, hmem⟩ : ℤ) : ℚ) ≤ (T : ℚ) * (U₀ : ℚ) := by
      rw [hcast]
      have hTpos' : (0 : ℚ) < (T : ℚ) := by exact_mod_cast T.pos
      nlinarith [hnorm.2, mul_le_mul_of_nonneg_left (hmu_le.trans hqR₀) hTpos'.le]
    have : ((aggExp hf2 ⟨tailh (ofFinsupp dv) h₀, hmem⟩ : ℤ) : ℚ) ≤ (((T : ℤ) * U₀ : ℤ) : ℚ) := by
      push_cast; exact hlt
    exact_mod_cast this
  -- ### the quantitative top-ray coefficient
  obtain ⟨J, u, hJcard, hu_supp, hu_blocks, -, hBval⟩ :=
    exists_top_ray_coeff μ.b_disjoint μ.card_b hr hhom hblocks hα0 hαp hγ₀0 hplace' n
  -- ### the carry-free collapse
  have hcol : IsCollapse (p := p) n D u.1 := by
    intro φ hsubD hcard hres
    have hmem : ∀ d ∈ φ.toMultiset, d ∈ D := fun d hd => hsubD ((Finsupp.mem_toMultiset _ _).mp hd)
    have hnorm : ((φ.toMultiset.map (DigitSeries.norm p)).sum - u.1.norm p).isInt = true := by
      rw [← map_multiset_sum, sum_toMultiset_eq_total]; exact hres
    obtain ⟨h1, h2⟩ := μ.carry_free hn hr hH hJcard u.2 hu_supp hu_blocks
      (ds := φ.toMultiset) (by rw [card_toMultiset_eq_card]; exact hcard)
      (fun d hd => hD d (hmem d hd))
      (fun d hd => by
        obtain ⟨m, dv, hdig, hq, hdeq⟩ := hD_eq_tail d (hmem d hd)
        rw [hdeq]; exact hclust m dv hdig hq) hnorm
    rw [card_toMultiset_eq_card] at h1
    rw [sum_toMultiset_eq_total] at h2
    exact ⟨h1, h2⟩
  obtain ⟨W, hW, hWval⟩ := exists_cosetSum_valued_le hf2 P hdeg.le hgR hval u.2
  rw [totalSum_eq_carryFree hD hf2 u.2 hcol P hdeg hW, Valuation.map_mul, hka T] at hWval
  -- ### the valuation contradiction
  have hC := le_of_eq (hkC T).symm
  have hBlow : ((Multiplicative.ofAdd (-((T : ℤ) * ((n : ℤ) * U₀ + (kC : ℤ)))) :
      Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      Valued.v ((DigitCoefficients.power (coefficientFamily p D (adFun hf2)) n) u) := by
    refine le_trans ?_ hBval
    rw [hγ₀, coe_ofAdd_neg_pow]
    calc
      ((Multiplicative.ofAdd (-((T : ℤ) * ((n : ℤ) * U₀ + (kC : ℤ)))) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        = ((Multiplicative.ofAdd (-((n : ℤ) * ((T : ℤ) * U₀))) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) *
          ((Multiplicative.ofAdd (-((T : ℤ) * kC)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.coe_mul, ← ofAdd_add]
          congr 2
          ring
      _ ≤ _ := mul_le_mul' le_rfl hC
  have hprod : ((Multiplicative.ofAdd (-((T : ℤ) * V₀)) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-((T : ℤ) * ka)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
        Valued.v ((DigitCoefficients.power (coefficientFamily p D (adFun hf2)) n) u) := by
    refine le_trans ?_ (mul_le_mul' le_rfl hBlow)
    rw [← WithZero.coe_mul, ← ofAdd_add, hV₀]
    exact le_of_eq (by congr 2; ring)
  have hfinal := hprod.trans hWval
  rw [WithZero.coe_le_coe, Multiplicative.ofAdd_le, neg_le_neg_iff] at hfinal
  omega

/-- **Finite-rank exclusion, core contradiction** (proof of Theorem 4.1). Let `f ∈ 𝕃_[p]` be
algebraic over `ℚ_[p]` with support in `[0, ∞)`, killed by `P ∈ ℤᶜᵘⁿ_[p][X]` of degree
`n ≥ 1`. If some truncation `S_{≤ R₀}` has order type `≥ ω ^ r` with `r ≥ 1` while every
truncation has order type `< ω ^ (r+1)`, we obtain a contradiction. At a sufficiently large
truncation, Proposition 3.1 bounds `v_p(P(f_{≤B}))` above, while the polynomial relation
forces it to exceed `B`. -/
theorem finite_rank_exclusion_core (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f)
    (hpos : ∀ q ∈ f.support, (0 : ℚ) ≤ q)
    (P : Polynomial ℤᶜᵘⁿ_[p]) (hPf : Polynomial.aeval f P = 0) {n : ℕ} (hn : 0 < n)
    (hdeg : P.natDegree = n) {r : ℕ} (hr : 0 < r) {R₀ : ℤ}
    (hU : omega0 ^ r ≤ typeLT ↥(f.support ∩ Set.Iic (R₀ : ℚ)))
    (hV : ∀ R : ℤ, typeLT ↥(f.support ∩ Set.Iic (R : ℚ)) < omega0 ^ (r + 1)) :
    False := by
  classical
  -- ### constants depending only on `f` and `P`
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [Polynomial.natDegree_zero] at hdeg
    omega
  have hlead : P.coeff n ≠ 0 := by
    rw [← hdeg]; exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  obtain ⟨ka, hka⟩ := exists_valued_oqpCUn_embd_eq hlead
  obtain ⟨kC, hkC⟩ := exists_valued_oqpCUn_embd_eq
    (p := p) (a := (interleavingConstant n r : ℤᶜᵘⁿ_[p]))
    (by
      intro h
      have h' := congrArg (algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p]) h
      rw [map_natCast, map_zero] at h'
      exact (Nat.cast_ne_zero.mpr (interleavingConstant_pos n r).ne' :
        (interleavingConstant n r : ℚᶜᵘⁿ_[p]) ≠ 0) h')
  have hkC' : ∀ T : ℕ+, Valued.v (interleavingConstant n r : ℚᶜᵘⁿ_[p,(T : ℕ)]) =
      ((Multiplicative.ofAdd (-((T : ℤ) * kC)) : Multiplicative ℤ) : WithZero _) := by
    intro T
    simpa only [map_natCast] using hkC T
  set V₀ : ℤ := (n : ℤ) * (R₀ + 1) + kC + ka with hV₀
  set R : ℤ := max R₀ V₀ + 1 with hRdef
  have hR₀R : R₀ < R := by omega
  have hRV : V₀ < R := by omega
  -- ### the truncation `g = f_{≤ R}`
  obtain ⟨g, e, hg, he, hfge⟩ := exists_truncation f R
  have hg_supp : g.support = f.support ∩ Set.Iic (R : ℚ) := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_Iic, mem_support_iff, hg]
    constructor
    · intro h
      by_cases hq : q ≤ (R : ℚ)
      · rw [if_pos hq] at h; exact ⟨h, hq⟩
      · rw [if_neg hq] at h; exact absurd rfl h
    · rintro ⟨h, hq⟩
      rw [if_pos hq]; exact h
  have hgR : ∀ q ∈ g.support, q ≤ (R : ℚ) := fun q hq => (hg_supp ▸ hq).2
  have hg_pos : ∀ q ∈ g.support, (0 : ℚ) ≤ q := fun q hq => hpos q (hg_supp ▸ hq).1
  -- ### QTR data of `g`
  obtain ⟨a, b, c, M, N, hqtr⟩ := exists_local_qtr f hf R
  rw [← hg] at hqtr
  have hwf : WellFoundedLT ↥(Function.support g.coeff) :=
    inferInstanceAs (WellFoundedLT ↥g.support)
  -- order-type hypotheses for the ray-marker lemma
  have hV' : typeLT ↥(Function.support g.coeff) < omega0 ^ (r + 1) := by
    have hEq : Function.support g.coeff = f.support ∩ Set.Iic (R : ℚ) := hg_supp
    rw [Ordinal.typeLT_set_congr hEq]
    exact hV R
  have hU' : omega0 ^ r ≤ typeLT ↥(Function.support g.coeff ∩ Set.Iic (R₀ : ℚ)) := by
    have hEq : Function.support g.coeff ∩ Set.Iic (R₀ : ℚ) = f.support ∩ Set.Iic (R₀ : ℚ) := by
      change g.support ∩ Set.Iic (R₀ : ℚ) = _
      rw [hg_supp, Set.inter_assoc, Set.Iic_inter_Iic]
      congr 2
      exact min_eq_right (by exact_mod_cast hR₀R.le)
    rw [Ordinal.typeLT_set_congr hEq]
    exact hU
  have hupper := uniform_polynomial_bound g hqtr hgR P hn hdeg
    hr hU' hV' hka hkC'
  have hfg : ((R : ℚ) : WithTop ℚ) < val p (f - g) := by
    have hfg_e : f - g = e := by rw [hfge]; ring
    rw [hfg_e]
    refine lt_val_of_forall_support fun q hq => ?_
    rw [mem_support_iff, he] at hq
    by_contra hle
    exact hq (if_pos (not_lt.mp hle))
  have hvf : (0 : WithTop ℚ) ≤ val p f :=
    le_val_of_forall_support fun q hq => by simpa using hpos q hq
  have hvg : (0 : WithTop ℚ) ≤ val p g :=
    le_val_of_forall_support fun q hq => by simpa using hg_pos q hq
  have hval := lt_val_aeval_truncation f g P hPf hvf hvg hfg
  have hlt : ((V₀ : ℚ) : WithTop ℚ) < ((R : ℚ) : WithTop ℚ) := by exact_mod_cast hRV
  exact (not_lt_of_ge hupper) (hlt.trans hval)

/-- An algebraic p-adic Hahn series with nonnegative support and order type below
`ω ^ ω` cannot have positive essential rank. By Lemma 2.12, this suffices for Theorem A, as
noted after Definition 2.13.

The essential truncation point fixes the uniform polynomial bound of Proposition 3.1.
Clearing denominators gives an integral polynomial relation, whose values at sufficiently
large truncations violate that bound. -/
theorem finite_rank_exclusion_of_essentialRank_pos
    (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f)
    (hpos : ∀ q ∈ f.support, (0 : ℚ) ≤ q) (hS : f.support.Nonempty)
    (hlt : typeLT f.support < omega0 ^ omega0) (hr : 0 < essentialRank hS hlt) : False := by
  classical
  -- an integral polynomial killing `f`
  have halgU : IsAlgebraic ℚᶜᵘⁿ_[p] f := pAdicHahnSeries.alg_QpCUn_of_alg_Qp p f hf
  obtain ⟨P', hP'0, hP'⟩ := halgU
  set P : Polynomial ℤᶜᵘⁿ_[p] :=
    IsLocalization.integerNormalization (nonZeroDivisors ℤᶜᵘⁿ_[p]) P' with hPdef
  have hPf : (Polynomial.aeval f) P = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ P' hP'
  have hPne : P ≠ 0 := by
    intro h0
    apply hP'0
    obtain ⟨b, hbmem, hbeq⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors ℤᶜᵘⁿ_[p]) P'
    rw [← hPdef, h0, Polynomial.map_zero] at hbeq
    have hbz : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
    ext i
    have hci : b • P'.coeff i = 0 := by
      rw [← Polynomial.coeff_smul, ← hbeq, Polynomial.coeff_zero]
    rw [Algebra.smul_def] at hci
    rcases mul_eq_zero.mp hci with hb0 | hcoeff
    · exact absurd (IsFractionRing.injective ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p]
        (by rw [map_zero]; exact hb0)) hbz
    · rw [hcoeff, Polynomial.coeff_zero]
  -- the degree is positive
  have hn : 0 < P.natDegree := by
    by_contra hzero
    have h0 : P.natDegree = 0 := by omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at hPf hPne
    rw [Polynomial.aeval_C] at hPf
    have hc : P.coeff 0 = 0 := by
      apply ZpUn_embd_injective (p := p)
      rw [map_zero]
      exact hPf
    exact hPne (by rw [hc, map_zero])
  exact finite_rank_exclusion_core f hf hpos P hPf hn rfl hr
    (essentialTruncationPoint_spec hS hlt).1
    (typeLT_inter_Iic_lt_omega0_pow_essentialRank_succ hS hlt)

/-- **Finite-rank exclusion for nonnegative supports**: Theorem 4.1 for an algebraic p-adic
Hahn series supported in `[0, ∞)` with order type below `ω ^ ω`. The positive essential rank
case is impossible; rank zero gives the conclusion by Lemma 2.12 (3). -/
theorem typeLT_support_le_omega0_of_lt_omega0_pow_omega0_of_nonneg
    (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f)
    (hpos : ∀ q ∈ f.support, (0 : ℚ) ≤ q) (hlt : typeLT f.support < omega0 ^ omega0) :
    typeLT f.support ≤ omega0 := by
  classical
  by_cases hS : f.support.Nonempty
  · by_cases hr0 : essentialRank hS hlt = 0
    · exact typeLT_le_omega0_of_essentialRank_eq_zero hS hlt hr0
    · exact False.elim (finite_rank_exclusion_of_essentialRank_pos f hf hpos hS hlt
        (Nat.pos_of_ne_zero hr0))
  · have hempty : f.support = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [Ordinal.typeLT_set_congr hempty]
    exact (le_of_eq (Ordinal.type_eq_zero_iff_isEmpty.mpr ⟨fun x ↦ x.2⟩)).trans omega0_pos.le

/-- **Finite-rank exclusion** (Theorem 4.1): the support of a `ℚ_[p]`-algebraic p-adic Hahn
series with order type below `ω ^ ω` has order type at most `ω`. A translation by an integer
reduces to nonnegative support. -/
theorem typeLT_support_le_omega0_of_lt_omega0_pow_omega0 (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f)
    (hlt : typeLT f.support < omega0 ^ omega0) :
    typeLT f.support ≤ omega0 := by
  classical
  by_cases hf0 : f = 0
  · subst hf0
    have : (0 : 𝕃_[p]).support = ∅ := by
      ext q; rw [mem_support_iff, coeff_zero_eq]; simp
    rw [Ordinal.typeLT_set_congr this]
    exact le_of_lt (lt_of_le_of_lt (le_of_eq (Ordinal.type_eq_zero_iff_isEmpty.mpr
      ⟨fun x => x.2⟩)) omega0_pos)
  · -- shift the support into `[0, ∞)`
    have hne : f.support.Nonempty := support_nonempty_of_nonzero p f hf0
    set q₀ : ℚ := (support_IsPWO f).isWF.min hne with hq₀
    have hq₀_le : ∀ q ∈ f.support, q₀ ≤ q := fun q hq => (support_IsPWO f).isWF.min_le hne hq
    set k : ℕ := ⌈-q₀⌉₊ with hk
    obtain ⟨f', -, hf'supp, hf'alg⟩ := exists_shift f k
    have hpos : ∀ q ∈ f'.support, (0 : ℚ) ≤ q := by
      intro q hq
      rw [hf'supp] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := hq₀_le q' hq'
      have h2 : -q₀ ≤ (k : ℚ) := Nat.le_ceil _
      linarith
    have hsupp_eq : f'.support = (fun q : ℚ => q + k) '' f.support := hf'supp
    have : WellFoundedLT ↥((fun q : ℚ => q + k) '' f.support) :=
      hsupp_eq ▸ inferInstanceAs (WellFoundedLT ↥f'.support)
    have htype : typeLT f'.support = typeLT f.support := by
      rw [Ordinal.typeLT_set_congr hsupp_eq]
      exact typeLT_image_add_right f.support (k : ℚ)
    rw [← htype] at hlt ⊢
    exact typeLT_support_le_omega0_of_lt_omega0_pow_omega0_of_nonneg f' (hf'alg hf) hpos hlt

end PAdicOrderType
