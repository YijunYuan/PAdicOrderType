/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateCriterion
import TrustworthyKedlaya.Kedlaya.PowAmplify
import TrustworthyKedlaya.Lp.AlgClosed

/-!
# Coset sums and the integral truncation estimate

This file formalizes the valuation part of the proof of Proposition 3.4 and the final
estimate in the proof of Theorem 4.1.

The original Witt-vector Hahn lift of `P(g)` differs from `P` evaluated at the
lift of `g` by a null series (`aeval_lift_sub_fromCoeff_mem_nullSeriesIdeal`), which gives
the identity (3.7).
`PAdicOrderType.RamifiedCoefficients.TNullSeriesIdeal_inter_image` gives the compatibility
of null series with the `1/T` coset sums, by splitting the integer index into
its residue classes modulo `T`.

For finite coefficient regrouping, the implementation reuses the bundled lift
`PAdicOrderType.CoefficientCosets.fhat`. Its coset sum agrees with that of the
canonical lift of `P(g)`. Bounded support makes the former sum finite, while
the valuation of `P(g)` bounds the latter (`exists_cosetSum_valued_le`).

For integral `f` and its closed truncation `g` at `R`, an integral polynomial relation
`P(f) = 0` gives `val P(g) > R` (`PAdicOrderType.lt_val_aeval_truncation`), as at the end of
the proof of Theorem 4.1.
-/

namespace PAdicOrderType

open RamifiedCoefficients CoefficientCosets TrustworthyKedlaya
  TrustworthyKedlaya.pAdicHahnSeries

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- **Closed truncation.** For `f ∈ 𝕃_[p]` and an integer `R`, `f = g + e` where `g` is the
truncation `f_{≤R}` of Section 1.1, with the coefficients of `f` at exponents `≤ R`, and `e`
those at exponents `> R`: the two Teichmüller expansions have disjoint supports, so they add
without carries. -/
theorem exists_truncation (f : 𝕃_[p]) (R : ℤ) :
    ∃ g e : 𝕃_[p], g.coeff = (fun q => if q ≤ (R : ℚ) then f.coeff q else 0) ∧
      e.coeff = (fun q => if q ≤ (R : ℚ) then 0 else f.coeff q) ∧ f = g + e := by
  classical
  set sg : ℚ → Fpbar p := fun q => if q ≤ (R : ℚ) then f.coeff q else 0 with hsg
  set se : ℚ → Fpbar p := fun q => if q ≤ (R : ℚ) then 0 else f.coeff q with hse
  have hsg_pwo : (Function.support sg).IsPWO := by
    refine (support_IsPWO f).mono fun q hq => ?_
    rw [Function.mem_support] at hq ⊢
    intro h0; change f.coeff q = 0 at h0; apply hq; simp [hsg, h0]
  have hse_pwo : (Function.support se).IsPWO := by
    refine (support_IsPWO f).mono fun q hq => ?_
    rw [Function.mem_support] at hq ⊢
    intro h0; change f.coeff q = 0 at h0; apply hq; simp [hse, h0]
  refine ⟨fromCoeff sg hsg_pwo, fromCoeff se hse_pwo, coeff_of_fromCoeff_eq_self sg hsg_pwo,
    coeff_of_fromCoeff_eq_self se hse_pwo, ?_⟩
  have hsum : sg + se = f.coeff := by
    funext q
    by_cases hq : q ≤ (R : ℚ) <;> simp [hsg, hse, hq]
  have hpwo : (Function.support (sg + se)).IsPWO := hsum ▸ support_IsPWO f
  rw [fromCoeff_add_of_disjoint_support sg se hsg_pwo hse_pwo hpwo (by
    intro q
    by_cases hq : q ≤ (R : ℚ)
    · exact Or.inr (by simp [hse, hq])
    · exact Or.inl (by simp [hsg, hq])), fromCoeff_congr hsum hpwo (support_IsPWO f),
    fromCoeff_of_coeff_eq_self]

/-- A lower bound on the support gives a lower bound on the valuation. -/
theorem le_val_of_forall_support {x : 𝕃_[p]} {c : ℚ} (hx : ∀ q ∈ x.support, c ≤ q) :
    (c : WithTop ℚ) ≤ val p x := by
  by_cases h0 : x = 0
  · rw [h0, val_zero_eq_top]; exact le_top
  · rw [val_apply, dif_neg h0]
    exact WithTop.coe_le_coe.mpr (hx _ ((support_IsPWO x).isWF.min_mem _))

/-- A strict lower bound on the support gives a strict lower bound on the valuation. -/
theorem lt_val_of_forall_support {x : 𝕃_[p]} {c : ℚ} (hx : ∀ q ∈ x.support, c < q) :
    (c : WithTop ℚ) < val p x := by
  by_cases h0 : x = 0
  · rw [h0, val_zero_eq_top]; exact WithTop.coe_lt_top c
  · rw [val_apply, dif_neg h0]
    exact WithTop.coe_lt_coe.mpr (hx _ ((support_IsPWO x).isWF.min_mem _))

/-- Strict version of `le_val_finset_sum`. -/
theorem lt_val_finset_sum {ι : Type*} (s : Finset ι) (x : ι → 𝕃_[p]) {g : WithTop ℚ}
    (hg : g ≠ ⊤) (h : ∀ i ∈ s, g < val p (x i)) : g < val p (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, val_zero_eq_top]
    exact lt_top_iff_ne_top.mpr hg
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (val p).map_lt_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `a + b + c` with `a ≥ α`, `b ≥ β`, `c > γ` (in `WithTop ℚ`) exceeds `α + β + γ`. -/
theorem coe_lt_add_add_of_le_of_le_of_lt {a b c : WithTop ℚ} {α β γ : ℚ}
    (ha : (α : WithTop ℚ) ≤ a) (hb : (β : WithTop ℚ) ≤ b) (hc : (γ : WithTop ℚ) < c) :
    ((α + β + γ : ℚ) : WithTop ℚ) < a + b + c := by
  by_cases hab : a + b = ⊤
  · rw [hab, top_add]; exact WithTop.coe_lt_top _
  · calc
      ((α + β + γ : ℚ) : WithTop ℚ) = ((α : WithTop ℚ) + β) + γ := by push_cast; rfl
      _ ≤ (a + b) + γ := add_le_add (add_le_add ha hb) le_rfl
      _ < a + b + c := WithTop.add_lt_add_left hab hc

/-- Witt-vector coefficients have nonnegative additive valuation. -/
lemma val_integral_nonneg (a : ℤᶜᵘⁿ_[p]) :
    (0 : WithTop ℚ) ≤ val p (algebraMap ℤᶜᵘⁿ_[p] 𝕃_[p] a) := by
  change (0 : WithTop ℚ) ≤ val p
    (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a))
  apply le_val_mkLp_of_coeff_eq_zero
  intro q hq
  rw [HahnSeries.coeff_single_of_ne (ne_of_lt hq)]

/-- **Truncation estimate**: if an integral polynomial vanishes at an integral
series `f`, and an integral series `g` satisfies `val (f - g) > R`, then the additive
valuation of `P(g)` is greater than `R`. This is the lower bound
`v_p(P(f_{≤B})) ≥ v_p(f_{≤B} - f) > B` at the end of the proof of Theorem 4.1. -/
theorem lt_val_aeval_truncation (f g : 𝕃_[p]) (P : Polynomial ℤᶜᵘⁿ_[p])
    (hPf : Polynomial.aeval f P = 0)
    (hf : (0 : WithTop ℚ) ≤ val p f) (hg : (0 : WithTop ℚ) ≤ val p g)
    {R : ℚ} (hfg : (R : WithTop ℚ) < val p (f - g)) :
    (R : WithTop ℚ) < val p (Polynomial.aeval g P) := by
  have hsplit : Polynomial.aeval g P =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        algebraMap ℤᶜᵘⁿ_[p] 𝕃_[p] (P.coeff i) * (g ^ i - f ^ i) := by
    have h1 : Polynomial.aeval g P = Polynomial.aeval g P - Polynomial.aeval f P := by
      rw [hPf, sub_zero]
    rw [h1, Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self _),
      Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self _), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, Algebra.smul_def, mul_sub]
  have hsub : (R : WithTop ℚ) < val p (g - f) := by
    rwa [← (val p).map_neg, neg_sub]
  rw [hsplit]
  refine lt_val_finset_sum _ _ WithTop.coe_ne_top fun i _ => ?_
  rw [← geom_sum₂_mul, (val p).map_mul, (val p).map_mul]
  have hgeom : (0 : WithTop ℚ) ≤ val p (∑ j ∈ Finset.range i, g ^ j * f ^ (i - 1 - j)) := by
    refine le_val_finset_sum _ _ fun j _ => ?_
    rw [(val p).map_mul]
    have h1 : (0 : WithTop ℚ) ≤ val p (g ^ j) := by simpa using le_val_pow hg j
    have h2 : (0 : WithTop ℚ) ≤ val p (f ^ (i - 1 - j)) := by
      simpa using le_val_pow hf (i - 1 - j)
    exact add_nonneg h1 h2
  simpa only [zero_add, add_assoc] using
    coe_lt_add_add_of_le_of_le_of_lt (val_integral_nonneg (P.coeff i)) hgeom hsub

section CosetSum

variable {g : 𝕃_[p]} {T : ℕ+} {D : Set DigitSeries}

/-- Polynomial evaluation in the original Witt-vector Hahn presentation differs
from the canonical lift of its value by a null series. In the proof of Proposition 3.4, this
says that `P(g̃) - h̃` is a null series, which gives the identity (3.7). -/
lemma aeval_lift_sub_fromCoeff_mem_nullSeriesIdeal (g : 𝕃_[p])
    (P : Polynomial ℤᶜᵘⁿ_[p]) :
    Polynomial.aeval (LiftedPAdicHahnSeries.fromCoeff g.coeff (support_IsPWO g)) P -
      LiftedPAdicHahnSeries.fromCoeff (Polynomial.aeval g P).coeff
        (support_IsPWO (Polynomial.aeval g P)) ∈ NullSeriesIdeal p := by
  rw [← Ideal.Quotient.eq]
  change Ideal.Quotient.mkₐ ℤᶜᵘⁿ_[p] (NullSeriesIdeal p)
      (Polynomial.aeval (LiftedPAdicHahnSeries.fromCoeff g.coeff (support_IsPWO g)) P) = _
  rw [← Polynomial.aeval_algHom_apply]
  change Polynomial.aeval (fromCoeff g.coeff (support_IsPWO g)) P =
    fromCoeff (Polynomial.aeval g P).coeff (support_IsPWO (Polynomial.aeval g P))
  rw [fromCoeff_of_coeff_eq_self, fromCoeff_of_coeff_eq_self]

/-- Evaluating a polynomial at the bundled Hahn lift differs from the Teichmüller
lift of its value by a ramified null series. Thus grouping coefficients by their digit
representative preserves all weighted coset sums (cf. the identity (3.7)). -/
theorem aeval_fhat_sub_fromCoeff_mem_tNullSeriesIdeal
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ g.support, -1 * (T : ℚ) * q = x})
    (P : Polynomial ℤᶜᵘⁿ_[p]) :
    (P.map (OQpCUn_embd p T)).aeval (fhat hf2) -
      TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) (Polynomial.aeval g P).coeff
        (support_IsPWO (Polynomial.aeval g P)) ∈ TNullSeriesIdeal p (T : ℕ) := by
  let G := LiftedPAdicHahnSeries.fromCoeff g.coeff (support_IsPWO g)
  let E := LiftedPAdicHahnSeries.fromCoeff (Polynomial.aeval g P).coeff
    (support_IsPWO (Polynomial.aeval g P))
  let ι := Lifted_to_TLifted p (T : ℕ)
  let I := TNullSeriesIdeal p (T : ℕ)
  have hbundle : Ideal.Quotient.mk I (fhat hf2) = Ideal.Quotient.mk I (ι G) := by
    apply Ideal.Quotient.eq.mpr
    have hlift : ι G = TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) g.coeff
        (support_IsPWO g) := by
      apply HahnSeries.ext
      funext q
      rfl
    rw [hlift]
    exact fhat_diff_isTNullSeries hf2
  have hpolynomial :
      (P.map (OQpCUn_embd p T)).aeval (fhat hf2) -
        (P.map (OQpCUn_embd p T)).aeval (ι G) ∈ I := by
    rw [← Ideal.Quotient.eq]
    change Ideal.Quotient.mkₐ ℤᶜᵘⁿ_[p,(T : ℕ)] I _ =
      Ideal.Quotient.mkₐ ℤᶜᵘⁿ_[p,(T : ℕ)] I _
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
    exact congrArg (fun x => (P.map (OQpCUn_embd p T)).aeval x) hbundle
  have hnull := (TNullSeriesIdeal_inter_image p (T : ℕ)
    (Polynomial.aeval G P - E)).mpr (aeval_lift_sub_fromCoeff_mem_nullSeriesIdeal g P)
  have hmap : ι (Polynomial.aeval G P) = (P.map (OQpCUn_embd p T)).aeval (ι G) := by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1
    apply RingHom.ext
    intro a
    change ι (HahnSeries.single 0 a) = HahnSeries.single 0 (OQpCUn_embd p T a)
    exact HahnSeries.map_single (a := (0 : ℚ)) (r := a)
      (f := (OQpCUn_embd p (T : ℕ) : ZeroHom ℤᶜᵘⁿ_[p] ℤᶜᵘⁿ_[p,(T : ℕ)]))
  change ι (Polynomial.aeval G P - E) ∈ I at hnull
  rw [map_sub, hmap] at hnull
  have hsum := I.add_mem hpolynomial hnull
  rw [sub_add_sub_cancel] at hsum
  exact hsum

/-- The `w`-th term of the `T`-null partial sums of `Y` on the coset of `g₀`. -/
noncomputable def cosetTerm (T : ℕ+) (Y : TLiftedPAdicHahnSeries p (T : ℕ)) (g₀ : ℚ) (w : ℤ) :
    ℚᶜᵘⁿ_[p,(T : ℕ)] :=
  pInvTQ p (T : ℕ) ^ w *
    algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)]) (Y.coeff (g₀ + (w : ℚ) / (T : ℚ)))

/-- The `M`-th `T`-null partial sum of `Y` on the coset of `g₀`. -/
noncomputable def cosetPartial (T : ℕ+) (Y : TLiftedPAdicHahnSeries p (T : ℕ)) (g₀ : ℚ)
    (M : ℕ) : ℚᶜᵘⁿ_[p,(T : ℕ)] :=
  ∑ w ∈ (TfiniteBelow p (T : ℕ) Y g₀ M).toFinset, cosetTerm T Y g₀ w

lemma cosetTerm_sub (Y Z : TLiftedPAdicHahnSeries p (T : ℕ)) (g₀ : ℚ) (w : ℤ) :
    cosetTerm T (Y - Z) g₀ w = cosetTerm T Y g₀ w - cosetTerm T Z g₀ w := by
  unfold cosetTerm
  rw [HahnSeries.coeff_sub, map_sub, mul_sub]

/-- The partial sum may be computed over any finite superset of the index set below `M`. -/
lemma cosetPartial_eq_sum (Y : TLiftedPAdicHahnSeries p (T : ℕ)) (g₀ : ℚ) (M : ℕ)
    {F : Finset ℤ} (hF : (TfiniteBelow p (T : ℕ) Y g₀ M).toFinset ⊆ F)
    (hFM : ∀ w ∈ F, g₀ + (w : ℚ) / (T : ℚ) ≤ (M : ℚ)) :
    cosetPartial T Y g₀ M = ∑ w ∈ F, cosetTerm T Y g₀ w := by
  unfold cosetPartial
  refine Finset.sum_subset hF fun w hwF hw => ?_
  have h0 : Y.coeff (g₀ + (w : ℚ) / (T : ℚ)) = 0 := by
    by_contra hne
    exact hw ((Set.Finite.mem_toFinset _).mpr ⟨hFM w hwF, hne⟩)
  unfold cosetTerm
  rw [h0, map_zero, mul_zero]

lemma cosetPartial_sub (Y Z : TLiftedPAdicHahnSeries p (T : ℕ)) (g₀ : ℚ) (M : ℕ) :
    cosetPartial T (Y - Z) g₀ M = cosetPartial T Y g₀ M - cosetPartial T Z g₀ M := by
  set F : Finset ℤ := (TfiniteBelow p (T : ℕ) (Y - Z) g₀ M).toFinset ∪
    (TfiniteBelow p (T : ℕ) Y g₀ M).toFinset ∪ (TfiniteBelow p (T : ℕ) Z g₀ M).toFinset with hF
  have hFM : ∀ w ∈ F, g₀ + (w : ℚ) / (T : ℚ) ≤ (M : ℚ) := by
    intro w hw
    rw [hF, Finset.mem_union, Finset.mem_union, Set.Finite.mem_toFinset,
      Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hw
    rcases hw with (h | h) | h <;> exact h.1
  have h1 : (TfiniteBelow p (T : ℕ) (Y - Z) g₀ M).toFinset ⊆ F := fun w hw =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hw)
  have h2 : (TfiniteBelow p (T : ℕ) Y g₀ M).toFinset ⊆ F := fun w hw =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hw)
  have h3 : (TfiniteBelow p (T : ℕ) Z g₀ M).toFinset ⊆ F := fun w hw =>
    Finset.mem_union_right _ hw
  rw [cosetPartial_eq_sum (Y - Z) g₀ M h1 hFM, cosetPartial_eq_sum Y g₀ M h2 hFM,
    cosetPartial_eq_sum Z g₀ M h3 hFM, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun w _ => cosetTerm_sub Y Z g₀ w

/-- The `T`-null condition, in terms of `cosetPartial`. -/
lemma tendsto_cosetPartial_of_mem {Y : TLiftedPAdicHahnSeries p (T : ℕ)}
    (hY : Y ∈ TNullSeriesIdeal p (T : ℕ)) (g₀ : ℚ) :
    Filter.Tendsto (cosetPartial T Y g₀) Filter.atTop (nhds 0) := by
  have h : IsTNullSeries p (T : ℕ) Y := hY
  have h₀ := h g₀
  refine h₀.congr fun M => ?_
  unfold cosetPartial cosetTerm
  exact Finset.sum_coe_sort (TfiniteBelow p (T : ℕ) Y g₀ M).toFinset
    (fun w : ℤ => pInvTQ p (T : ℕ) ^ w *
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)]) (Y.coeff (g₀ + (w : ℚ) / (T : ℚ))))

/-- The coefficients of `P(ĝ)` vanish above `n · max(R, 0)` when `Supp g ⊆ (-∞, R]`. -/
lemma aeval_fhat_coeff_eq_zero_of_degree_bound_mul_lt
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ g.support, -1 * (T : ℚ) * q = x})
    (P : Polynomial ℤᶜᵘⁿ_[p]) {n : ℕ} (hdeg : P.natDegree ≤ n)
    {R : ℤ} (hgR : ∀ q ∈ g.support, q ≤ (R : ℚ)) {q : ℚ} (hq : ((n * R.toNat : ℕ) : ℚ) < q) :
    ((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff q = 0 := by
  rw [aeval_fhat_coeff_eq hf2 P hdeg q]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsupp : Function.support (fhat hf2).coeff ⊆ {x : ℚ | x ≤ (R : ℚ)} := fun x hx =>
    hgR x (Stilde_subset_support hf2 (fhat_support_subset hf2 hx))
  have hzero : ((fhat hf2) ^ i).coeff q = 0 := by
    by_contra hne
    have hq_mem : q ∈ ((fhat hf2) ^ i).support := by
      simpa [HahnSeries.mem_support] using hne
    obtain ⟨l, hlc, hlm, hls⟩ := exists_multiset_of_mem_support_pow hsupp i hq_mem
    have hsum : l.sum ≤ Multiset.card l • (R : ℚ) :=
      Multiset.sum_le_card_nsmul l (R : ℚ) fun x hx => hlm x hx
    rw [hls, hlc, nsmul_eq_mul] at hsum
    have hR : (R : ℚ) ≤ ((R.toNat : ℕ) : ℚ) := by exact_mod_cast Int.self_le_toNat R
    have hiR : (i : ℚ) * (R : ℚ) ≤ ((n * R.toNat : ℕ) : ℚ) := by
      push_cast
      calc
        (i : ℚ) * (R : ℚ) ≤ (i : ℚ) * ((R.toNat : ℕ) : ℚ) :=
            mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg i)
        _ ≤ (n : ℚ) * ((R.toNat : ℕ) : ℚ) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hi') (Nat.cast_nonneg _)
    linarith
  rw [hzero, mul_zero]

/-- **Coset-sum valuation bound** (the final step of the proof of Proposition 3.4): suppose
`g` has support bounded above and the
additive valuation of `P(g)` exceeds an integer `R'`. For a proper digit vector `u`,
only finitely many coefficients of the polynomial evaluated at the bundled lift contribute
on the coset `-‖u‖ / T + (1/T)ℤ`.

Their weighted sum has multiplicative valuation at most `ofAdd (-(T * R' + 1))` in the
ramified fraction field. This is an additive p-adic valuation strictly greater than `R'`
when normalized by `v_p(p) = 1`. The bound follows by comparison with the coset sum of
the Teichmüller lift of `P(g)`. -/
theorem exists_cosetSum_valued_le
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ g.support, -1 * (T : ℚ) * q = x})
    (P : Polynomial ℤᶜᵘⁿ_[p]) {n : ℕ} (hdeg : P.natDegree ≤ n)
    {R : ℤ} (hgR : ∀ q ∈ g.support, q ≤ (R : ℚ))
    {R' : ℤ} (hval : ((R' : ℚ) : WithTop ℚ) < val p (Polynomial.aeval g P))
    {u : DigitSeries} (hu : u.IsP p) :
    ∃ W : Finset ℤ,
      (∀ w : ℤ, w ∉ W →
        ((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
          (-(u.norm p : ℚ) / (T : ℚ) + (w : ℚ) / (T : ℚ)) = 0) ∧
      Valued.v (∑ w ∈ W, pInvTQ p (T : ℕ) ^ w *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
          (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
            (-(u.norm p : ℚ) / (T : ℚ) + (w : ℚ) / (T : ℚ)))) ≤
        ((Multiplicative.ofAdd (-((T : ℤ) * R' + 1)) : Multiplicative ℤ) : WithZero _) := by
  classical
  set X := (P.map (OQpCUn_embd p T)).aeval (fhat hf2) with hX
  set E := TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) (Polynomial.aeval g P).coeff
    (support_IsPWO (Polynomial.aeval g P)) with hE
  set g₀ : ℚ := -(u.norm p : ℚ) / (T : ℚ) with hg₀
  set γ : WithZero (Multiplicative ℤ) :=
    ((Multiplicative.ofAdd (-((T : ℤ) * R' + 1)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with hγ
  have hTpos : (0 : ℚ) < (T : ℚ) := by exact_mod_cast T.pos
  -- the index set of the non-zero coefficients of `X` on the coset
  set M₀ : ℕ := n * R.toNat with hM₀
  set W : Finset ℤ := (TfiniteBelow p (T : ℕ) X g₀ M₀).toFinset with hW
  have hXbound : ∀ w : ℤ, X.coeff (g₀ + (w : ℚ) / (T : ℚ)) ≠ 0 →
      g₀ + (w : ℚ) / (T : ℚ) ≤ (M₀ : ℚ) := by
    intro w hw
    by_contra hlt
    exact hw (aeval_fhat_coeff_eq_zero_of_degree_bound_mul_lt hf2 P hdeg hgR (not_le.mp hlt))
  have hWmem : ∀ w : ℤ, w ∈ W ↔ X.coeff (g₀ + (w : ℚ) / (T : ℚ)) ≠ 0 := by
    intro w
    rw [hW, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hXbound w h, h⟩⟩
  refine ⟨W, fun w hw => by simpa using (not_iff_not.mpr (hWmem w)).mp hw, ?_⟩
  -- the total sum
  set total : ℚᶜᵘⁿ_[p,(T : ℕ)] := ∑ w ∈ W, cosetTerm T X g₀ w with htotal
  change Valued.v total ≤ γ
  -- the partial sums of `X` are eventually equal to `total`
  have hXpartial : ∀ M : ℕ, M₀ ≤ M → cosetPartial T X g₀ M = total := by
    intro M hM
    unfold cosetPartial
    rw [htotal]
    congr 1
    ext w
    rw [Set.Finite.mem_toFinset, hWmem]
    exact ⟨fun h => h.2, fun h => ⟨(hXbound w h).trans (by exact_mod_cast hM), h⟩⟩
  -- the partial sums of `E` converge to `total`
  have hnull := tendsto_cosetPartial_of_mem
    (aeval_fhat_sub_fromCoeff_mem_tNullSeriesIdeal hf2 P) g₀
  have hE_tendsto : Filter.Tendsto (cosetPartial T E g₀) Filter.atTop (nhds total) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have h1 : Filter.Tendsto (fun M => -(cosetPartial T E g₀ M - total)) Filter.atTop
        (nhds 0) := by
      refine hnull.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
      rw [cosetPartial_sub, hXpartial M hM, neg_sub]
    simpa using h1.neg
  -- every partial sum of `E` has valuation `≤ γ`
  have hEval : ∀ M : ℕ, Valued.v (cosetPartial T E g₀ M) ≤ γ := by
    intro M
    unfold cosetPartial
    refine Valuation.map_sum_le _ fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    -- the exponent exceeds `R'`
    have hcoeff : (Polynomial.aeval g P).coeff (g₀ + (w : ℚ) / (T : ℚ)) ≠ 0 := by
      intro h0
      apply hw.2
      change OQpCUn_embd p (T : ℕ) (WittVector.teichmuller p
        ((Polynomial.aeval g P).coeff (g₀ + (w : ℚ) / (T : ℚ)))) = 0
      rw [h0, WittVector.teichmuller_zero, map_zero]
    have hR'q : (R' : ℚ) < g₀ + (w : ℚ) / (T : ℚ) := by
      have h1 := val_le_of_coeff_ne_zero hcoeff
      exact WithTop.coe_lt_coe.mp (lt_of_lt_of_le hval h1)
    have hg₀ : g₀ ≤ 0 := by
      rw [hg₀]
      have := (DigitSeries.norm_mem_Ico p u hu).1
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr this) hTpos.le
    have hwR : (T : ℤ) * R' + 1 ≤ w := by
      have h2 : ((T : ℤ) : ℚ) * (R' : ℚ) < (w : ℚ) := by
        have h3 : (R' : ℚ) < (w : ℚ) / (T : ℚ) := by linarith
        have h4 := (lt_div_iff₀ hTpos).mp h3
        push_cast
        linarith
      have h5 : (T : ℤ) * R' < w := by exact_mod_cast h2
      omega
    unfold cosetTerm
    rw [Valuation.map_mul, valued_v_pInvT_zpow]
    have h_alg : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
        (E.coeff (g₀ + (w : ℚ) / (T : ℚ)))) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,(T : ℕ)])).valuation_le_one _
    calc
      ((Multiplicative.ofAdd (-w : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
            (E.coeff (g₀ + (w : ℚ) / (T : ℚ))))
        ≤ ((Multiplicative.ofAdd (-w : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
          mul_le_mul' le_rfl h_alg
      _ = ((Multiplicative.ofAdd (-w : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
      _ ≤ γ := by
          rw [hγ, WithZero.coe_le_coe]
          exact Multiplicative.ofAdd_le.mpr (by omega)
  -- closedness of the valuation ball
  by_contra hcon
  push Not at hcon
  have hγ0 : γ ≠ 0 := WithZero.coe_ne_zero
  have htot0 : Valued.v total ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le (a := γ)) hcon)
  have hball := Tmem_nhds_v_sub_lt (p := p) (T := (T : ℕ)) (x := total) htot0 rfl
  obtain ⟨M, hM⟩ := (hE_tendsto.eventually hball).exists
  have heq : Valued.v (cosetPartial T E g₀ M) = Valued.v total :=
    Valuation.map_eq_of_sub_lt _ hM
  exact absurd (heq ▸ hEval M) (not_le.mpr hcon)

end CosetSum

end PAdicOrderType
