/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.References.HyperAlgebraic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TrustworthyKedlaya.Kedlaya.ShadowCollapse
import TrustworthyKedlaya.Lp.Embedding

/-!
# The field of strict `p`-adic Puiseux series

We identify the `ℚ_[p]`-algebraic elements of `𝕃_[p]` with the algebraic closure `PadicAlgCl p`
(through the embedding `PadicAlgCl p → ℂ_[p] → 𝕃_[p]`), descend the `p`-radicals `p^(1/T)` of
`𝕃_[p]` to `PadicAlgCl p`, and define the field of strict `p`-adic Puiseux series

`⋃_{T ≥ 1} ℚᵘⁿ_[p](p^(1/T))`

as a subfield of `PadicAlgCl p`. This is the field appearing in Theorem C and
Propositions 4.3 and 4.4, and the radicals are the elements `p^q` of Section 1.1. The theorem
`exists_pAdicStrictPuiseux_iff` characterizes its image in `𝕃_[p]` by uniformly bounded
exponent denominators and finite coefficient range.
-/

namespace PAdicOrderType

open TrustworthyKedlaya TrustworthyKedlaya.pAdicHahnSeries Polynomial

open scoped IntermediateField

/-- A `p`-adic Hahn series is algebraic over `ℚ_[p]` if and only if it lies in the image of the
algebraic closure `PadicAlgCl p` of `ℚ_[p]` (the preimage is unique by `algClEmbd_injective`). -/
theorem isAlgebraic_qp_iff_mem_range_padicAlgCl {p : ℕ} [Fact p.Prime] (x : 𝕃_[p]) :
    IsAlgebraic ℚ_[p] x ↔ x ∈ {(y : 𝕃_[p]) | y : PadicAlgCl p} := by
  constructor
  · rintro ⟨P, hP, hPx⟩
    have hsplit : (P.map (algebraMap ℚ_[p] (PadicAlgCl p))).Splits := IsAlgClosed.splits _
    have hxmem : x ∈ P.rootSet 𝕃_[p] := mem_rootSet.mpr ⟨hP, hPx⟩
    rw [← hsplit.image_rootSet (algClEmbd p)] at hxmem
    obtain ⟨y, -, hy⟩ := hxmem
    exact ⟨y, (coe_coe y).trans hy⟩
  · rintro ⟨y, hy⟩
    rw [← hy, coe_coe]
    exact (Algebra.IsAlgebraic.isAlgebraic y).algHom (algClEmbd p)

/-- The `p`-radical `p^(1/T) = [1]·p^(1/T)` of `𝕃_[p]` is algebraic over `ℚ_[p]`: its `T`-th
power is `p`. -/
lemma pRadical_isAlgebraic_qp {p : ℕ} [Fact p.Prime] (T : ℕ+) :
    IsAlgebraic ℚ_[p] (single T⁻¹ 1 : 𝕃_[p]) := by
  rw [isAlgebraic_iff_isIntegral]
  refine IsIntegral.of_pow T.pos ?_
  have hT : ((T : ℕ) : ℚ) * (T : ℚ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast T.ne_zero)
  rw [pAdicHahnSeries.single_pow, one_pow, hT, ← p_eq_single_one]
  exact isIntegral_natCast p

/-- The element `p^(1/T)` of the algebraic closure of `ℚ_[p]`: the unique element of
`PadicAlgCl p` whose image in `𝕃_[p]` is the one-term series `[1]·p^(1/T)`. This is the root
of `X ^ T - p` fixed by the chosen embedding, as in Section 1.1. -/
noncomputable def pRadical (p : ℕ) [Fact p.Prime] (T : ℕ+) : PadicAlgCl p :=
  ((isAlgebraic_qp_iff_mem_range_padicAlgCl (single T⁻¹ 1 : 𝕃_[p])).1
    (pRadical_isAlgebraic_qp T)).choose

section pRadical

variable {p : ℕ} [Fact p.Prime]

/-- The image of `p^(1/T)` in `𝕃_[p]` is the one-term series `[1]·p^(1/T)`. -/
theorem coe_pRadical (T : ℕ+) : (pRadical p T : 𝕃_[p]) = single T⁻¹ 1 :=
  ((isAlgebraic_qp_iff_mem_range_padicAlgCl (single T⁻¹ 1 : 𝕃_[p])).1
    (pRadical_isAlgebraic_qp T)).choose_spec

/-- `p^(1/T)` is characterised by its image in `𝕃_[p]`. -/
theorem eq_pRadical_of_coe_eq {T : ℕ+} {y : PadicAlgCl p} (hy : (y : 𝕃_[p]) = single T⁻¹ 1) :
    y = pRadical p T :=
  algClEmbd_injective <| by rw [← coe_coe, ← coe_coe, hy, coe_pRadical]

/-- `(p^(1/(T S)))^S = p^(1/T)`. -/
theorem pRadical_mul_pow (T S : ℕ+) : pRadical p (T * S) ^ (S : ℕ) = pRadical p T := by
  refine eq_pRadical_of_coe_eq ?_
  rw [coe_coe, map_pow, ← coe_coe, coe_pRadical, pAdicHahnSeries.single_pow, one_pow]
  congr 1
  push_cast
  field_simp

/-- The tower `ℚᵘⁿ_[p](p^(1/T)) ⊆ ℚᵘⁿ_[p](p^(1/(T S)))`. -/
theorem adjoin_pRadical_le_adjoin_pRadical_mul (T S : ℕ+) :
    ℚᵘⁿ_[p]⟮pRadical p T⟯ ≤ ℚᵘⁿ_[p]⟮pRadical p (T * S)⟯ := by
  rw [IntermediateField.adjoin_simple_le_iff, ← pRadical_mul_pow T S]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _

/-- The fields obtained by adjoining the compatible radicals form a directed family: the
radical indexed by a product contains the fields indexed by either factor. -/
theorem directed_adjoin_pRadical :
    Directed (· ≤ ·) fun T : ℕ+ ↦ ℚᵘⁿ_[p]⟮pRadical p T⟯ := fun T S ↦
  ⟨T * S, adjoin_pRadical_le_adjoin_pRadical_mul T S,
    mul_comm T S ▸ adjoin_pRadical_le_adjoin_pRadical_mul S T⟩

end pRadical

/-- **The field of strict `p`-adic Puiseux series** `⋃_{T ≥ 1} ℚᵘⁿ_[p](p^(1/T))`, as a subfield of
the algebraic closure `PadicAlgCl p` of `ℚ_[p]`. This is the field of Theorem C, denoted `F`
in the proof of Proposition 4.3. -/
noncomputable def pAdicStrictPuiseux (p : ℕ) [Fact p.Prime] : Subfield (PadicAlgCl p) :=
  (⨆ T : ℕ+, ℚᵘⁿ_[p]⟮pRadical p T⟯).toSubfield

/-- An element of `PadicAlgCl p` is a strict `p`-adic Puiseux series if and only if it lies in
`ℚᵘⁿ_[p](p^(1/T))` for some `T ≥ 1`. -/
theorem mem_pAdicStrictPuiseux_iff {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p} :
    x ∈ pAdicStrictPuiseux p ↔ ∃ T : ℕ+, x ∈ ℚᵘⁿ_[p]⟮pRadical p T⟯ := by
  rw [pAdicStrictPuiseux, IntermediateField.mem_toSubfield, ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed directed_adjoin_pRadical, Set.mem_iUnion]
  simp only [SetLike.mem_coe]

/-- Every chosen positive integral root of `p` belongs to the strict p-adic Puiseux field. -/
theorem pRadical_mem_pAdicStrictPuiseux {p : ℕ} [Fact p.Prime] (T : ℕ+) :
    pRadical p T ∈ pAdicStrictPuiseux p :=
  mem_pAdicStrictPuiseux_iff.mpr ⟨T, IntermediateField.mem_adjoin_simple_self _ _⟩

/-- The image of the maximal unramified extension lies in the strict p-adic Puiseux field. -/
theorem qpUn_toAlgCl_mem_pAdicStrictPuiseux {p : ℕ} [Fact p.Prime] (x : ℚᵘⁿ_[p]) :
    (x : PadicAlgCl p) ∈ pAdicStrictPuiseux p :=
  mem_pAdicStrictPuiseux_iff.mpr ⟨1, IntermediateField.algebraMap_mem _ x⟩

section Equivalence

open Topology

variable {p : ℕ} [Fact p.Prime]

/-! ### Preservation of the exponent lattice -/

/-- Restricting to a union of integer cosets preserves null series. -/
private lemma hahnRestrict_mem_nullSeries (S : Set ℚ)
    (hS : ∀ (g : ℚ) (n : ℤ), g + n ∈ S ↔ g ∈ S)
    (x : LiftedPAdicHahnSeries p) (hx : x ∈ NullSeriesIdeal p) :
    hahnRestrict S x ∈ NullSeriesIdeal p := by
  classical
  change IsNullSeries _
  intro g
  by_cases hg : g ∈ S
  · have heq (M : ℕ) : (finiteBelow (hahnRestrict S x) g M).toFinset =
        (finiteBelow x g M).toFinset := by
      ext n
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      rw [coeff_hahnRestrict_of_mem x ((hS g n).mpr hg)]
    convert hx g using 1
    funext M
    rw [heq]
    apply Finset.sum_congr rfl
    intro n hn
    rw [coeff_hahnRestrict_of_mem x ((hS g n).mpr hg)]
  · have hzero (n : ℤ) : (hahnRestrict S x).coeff (g + n) = 0 :=
      coeff_hahnRestrict_of_notMem x (fun h => hg ((hS g n).mp h))
    convert tendsto_const_nhds (x := (0 : ℚᶜᵘⁿ_[p])) using 1
    funext M
    apply Finset.sum_eq_zero
    intro n hn
    rw [hzero, map_zero, mul_zero]

/-- Canonicalization preserves every additive subgroup of exponents containing `1`:
the restriction of the canonical representative to its complement is a null series. -/
private lemma support_mk_subset_addSubgroup (G : AddSubgroup ℚ) (h1 : (1 : ℚ) ∈ G)
    (x : LiftedPAdicHahnSeries p) (hx : x.support ⊆ G) :
    pAdicHahnSeries.support (Ideal.Quotient.mk (NullSeriesIdeal p) x) ⊆ (G : Set ℚ) := by
  classical
  let f : 𝕃_[p] := Ideal.Quotient.mk (NullSeriesIdeal p) x
  let s : ℚ → 𝔽ᵃ_[p] := (G : Set ℚ)ᶜ.indicator f.coeff
  have hs : (Function.support s).IsPWO := (support_IsPWO f).mono
    (by
      intro q hq h
      change f.coeff q = 0 at h
      apply hq
      by_cases hqG : q ∈ G <;> simp [s, hqG, h])
  have hn : x - LiftedPAdicHahnSeries.fromCoeff f.coeff (support_IsPWO f) ∈ NullSeriesIdeal p := by
    apply Ideal.Quotient.eq.mp
    exact (fromCoeff_of_coeff_eq_self f).symm
  have hshift (g : ℚ) (n : ℤ) : g + n ∈ (G : Set ℚ)ᶜ ↔ g ∈ (G : Set ℚ)ᶜ := by
    have hn : (n : ℚ) ∈ G := by simpa using G.zsmul_mem h1 n
    simp only [Set.mem_compl_iff]
    exact not_congr (G.add_mem_cancel_right hn)
  have hres := hahnRestrict_mem_nullSeries (G : Set ℚ)ᶜ hshift _ hn
  have heq : hahnRestrict (G : Set ℚ)ᶜ
      (x - LiftedPAdicHahnSeries.fromCoeff f.coeff (support_IsPWO f)) =
      -LiftedPAdicHahnSeries.fromCoeff s hs := by
    apply HahnSeries.ext
    funext q
    by_cases hq : q ∈ G
    · rw [coeff_hahnRestrict_of_notMem _ (by simpa)]
      simp [HahnSeries.coeff_neg, LiftedPAdicHahnSeries.fromCoeff, s, hq]
    · rw [coeff_hahnRestrict_of_mem _ hq, HahnSeries.coeff_sub, HahnSeries.coeff_neg]
      have hxq : x.coeff q = 0 := by by_contra h; exact hq (hx h)
      simp [LiftedPAdicHahnSeries.fromCoeff, s, hq, hxq]
  rw [heq, neg_mem_iff] at hres
  have hfzero : fromCoeff s hs = (0 : 𝕃_[p]) := Ideal.Quotient.eq_zero_iff_mem.mpr hres
  have hcoeff := congrArg (fun y : 𝕃_[p] => y.coeff) hfzero
  rw [coeff_of_fromCoeff_eq_self, coeff_zero_eq] at hcoeff
  intro q hq
  by_contra hqG
  have h := congrFun hcoeff q
  have : f.coeff q = 0 := by simpa [s, hqG] using h
  exact hq this

/-- Lifted Hahn series whose exponents lie in the additive subgroup `G`. -/
private noncomputable def liftedSupportSubring (G : AddSubgroup ℚ) :
    Subring (LiftedPAdicHahnSeries p) where
  carrier := {x | x.support ⊆ G}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy := Set.Subset.trans (HahnSeries.support_add_subset _ _) (by
    rintro q (hq | hq)
    · exact hx hq
    · exact hy hq)
  neg_mem' hx := by simpa using hx
  mul_mem' hx hy := Set.Subset.trans HahnSeries.support_mul_subset (by
    rintro q ⟨a, ha, b, hb, rfl⟩
    exact G.add_mem (hx ha) (hy hb))

private lemma single_mem_liftedSupportSubring (G : AddSubgroup ℚ) {q : ℚ} (hq : q ∈ G)
    (a : ℤᶜᵘⁿ_[p]) : HahnSeries.single q a ∈ liftedSupportSubring G := by
  intro r hr
  have : r = q := HahnSeries.support_single_subset hr
  simpa [this] using hq

private lemma algebraMap_mem_liftedSupportSubring_map (G : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ G) (x : ℚᶜᵘⁿ_[p]) :
    algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] x ∈
      (liftedSupportSubring G).map (Ideal.Quotient.mk (NullSeriesIdeal p)) := by
  let R := (liftedSupportSubring G).map (Ideal.Quotient.mk (NullSeriesIdeal p))
  have hconst (a : ℤᶜᵘⁿ_[p]) : ZpUn_embd a ∈ R :=
    Subring.mem_map.mpr ⟨HahnSeries.single 0 a, single_mem_liftedSupportSubring G G.zero_mem a, rfl⟩
  have hpow (k : ℕ) : ((p : 𝕃_[p]) ^ k)⁻¹ ∈ R := by
    have hsingle : single (-(k : ℚ)) (1 : 𝔽ᵃ_[p]) ∈ R := by
      rw [single, fromCoeff, lifted_fromCoeff_single]
      exact Subring.mem_map.mpr ⟨_, single_mem_liftedSupportSubring G (by
        simpa using G.neg_mem (G.nsmul_mem h1 k)) _, rfl⟩
    convert hsingle using 1
    apply inv_eq_of_mul_eq_one_right
    rw [p_pow_eq_single, single_mul_single, add_neg_cancel, one_mul, single_zero_one]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤᶜᵘⁿ_[p]) x
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hb) (WittVector.irreducible p)
  simp only [map_inv₀, map_mul, map_pow, map_natCast, algebraMap_QpCUn_algebraMap,
    div_eq_mul_inv, mul_inv_rev]
  change ZpUn_embd a * (((p : 𝕃_[p]) ^ k)⁻¹ * (ZpUn_embd (u : ℤᶜᵘⁿ_[p]))⁻¹) ∈ R
  rw [← map_units_inv]
  exact R.mul_mem (hconst a) (R.mul_mem (hpow k) (hconst ↑u⁻¹))

private lemma bounded_denominators_of_mem_pAdicStrictPuiseux (x : pAdicStrictPuiseux p) :
    ∃ T : ℕ+, ∀ q ∈ (x : 𝕃_[p]).support, ((T : ℚ) * q).isInt := by
  obtain ⟨T, hx⟩ := mem_pAdicStrictPuiseux_iff.mp x.property
  let G : AddSubgroup ℚ := AddSubgroup.zmultiples (T : ℚ)⁻¹
  have h1 : (1 : ℚ) ∈ G := by
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨(T : ℕ), ?_⟩
    simp [zsmul_eq_mul]
  let R : Subring 𝕃_[p] := (liftedSupportSubring G).map (Ideal.Quotient.mk (NullSeriesIdeal p))
  let A : Subalgebra ℚᵘⁿ_[p] 𝕃_[p] :=
    { R with
      algebraMap_mem' := fun y => algebraMap_mem_liftedSupportSubring_map G h1 (y : ℚᶜᵘⁿ_[p]) }
  have hr : algClEmbdQpUn p (pRadical p T) ∈ A := by
    change algClEmbd p (pRadical p T) ∈ R
    rw [← coe_coe, coe_pRadical, single, fromCoeff, lifted_fromCoeff_single]
    exact Subring.mem_map.mpr ⟨_, single_mem_liftedSupportSubring G
      (AddSubgroup.mem_zmultiples _) _, rfl⟩
  have hxA : algClEmbdQpUn p x.val ∈ A := by
    have hx' : x.val ∈ Algebra.adjoin ℚᵘⁿ_[p] {pRadical p T} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic (pRadical p T))]
      exact hx
    exact (Algebra.adjoin_le (by simpa using hr) :
      Algebra.adjoin ℚᵘⁿ_[p] {pRadical p T} ≤ A.comap (algClEmbdQpUn p)) hx'
  obtain ⟨y, hy, hyeq⟩ := Subring.mem_map.mp hxA
  have hsupport := support_mk_subset_addSubgroup G h1 y hy
  refine ⟨T, fun q hq => ?_⟩
  have hqG : q ∈ G := by
    apply hsupport
    rw [hyeq]
    simpa only [coe_coe, algClEmbd_apply] using hq
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hqG
  rw [← hn, zsmul_eq_mul]
  have heq : (T : ℚ) * ((n : ℚ) * (T : ℚ)⁻¹) = n := by field_simp
  rw [heq]
  simp [Rat.isInt]

/-! ### Finite truncations and closed finite extensions -/

private lemma exists_pAdicStrictPuiseux_coe_eq_teichmuller (a : 𝔽ᵃ_[p]) :
    ∃ x : pAdicStrictPuiseux p, (x : 𝕃_[p]) = single 0 a := by
  let y : ℚᵘⁿ_[p] := ⟨algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] (WittVector.teichmuller p a),
    QpUn.algebraMap_mem p (teichmuller_mem_OQpUn p a)⟩
  refine ⟨⟨(y : PadicAlgCl p), qpUn_toAlgCl_mem_pAdicStrictPuiseux y⟩, ?_⟩
  change ((y : PadicAlgCl p) : 𝕃_[p]) = _
  rw [coe_coe_toAlgCl, algebraMap_QpUn_apply]
  change algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]
    (algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] (WittVector.teichmuller p a)) = _
  rw [algebraMap_QpCUn_algebraMap]
  rw [single, fromCoeff, lifted_fromCoeff_single]
  rfl

/-- A support with bounded denominators has only finitely many points below any cutoff. -/
lemma finite_support_inter_Iio_of_bounded_denominators (f : 𝕃_[p]) (T : ℕ+)
    (hT : ∀ q ∈ f.support, ((T : ℚ) * q).isInt) (r : ℚ) :
    (f.support ∩ Set.Iio r).Finite := by
  classical
  by_cases hf : f.support.Nonempty
  · let b := (support_IsPWO f).isWF.min hf
    have hb : ∀ q ∈ f.support, b ≤ q := fun q hq =>
      (support_IsPWO f).isWF.min_le hf hq
    have hpos : (0 : ℚ) < T := by exact_mod_cast T.pos
    have hfinite : ((fun q : ℚ => ((T : ℚ) * q).num) ''
        (f.support ∩ Set.Iio r)).Finite := by
      apply (Set.finite_Icc ⌈(T : ℚ) * b⌉ ⌊(T : ℚ) * r⌋).subset
      rintro n ⟨q, ⟨hq, hqr⟩, rfl⟩
      have heq := Rat.eq_num_of_isInt (hT q hq)
      constructor
      · apply Int.ceil_le.mpr
        rw [← heq]
        exact mul_le_mul_of_nonneg_left (hb q hq) hpos.le
      · apply Int.le_floor.mpr
        rw [← heq]
        exact (mul_lt_mul_of_pos_left hqr hpos).le
    apply hfinite.of_finite_image
    intro q hq u hu heq
    apply mul_left_cancel₀ (ne_of_gt hpos) (a := (T : ℚ))
    rw [Rat.eq_num_of_isInt (hT q hq.1), Rat.eq_num_of_isInt (hT u hu.1)]
    exact_mod_cast heq
  · simp [Set.not_nonempty_iff_eq_empty.mp hf]

/-- The finite truncation below `r` agrees with the series at all exponents below `r`. -/
lemma le_val_sub_sum_support_below (f : 𝕃_[p]) (r : ℚ)
    (hfin : (f.support ∩ Set.Iio r).Finite) :
    (r : WithTop ℚ) ≤ val p
      (f - ∑ q ∈ hfin.toFinset, single q (f.coeff q)) := by
  classical
  have heq : f - ∑ q ∈ hfin.toFinset, single q (f.coeff q) =
      Ideal.Quotient.mk (NullSeriesIdeal p)
        (LiftedPAdicHahnSeries.fromCoeff f.coeff (support_IsPWO f) -
          ∑ q ∈ hfin.toFinset, HahnSeries.single q (WittVector.teichmuller p (f.coeff q))) := by
    rw [map_sub, map_sum]
    congr 1
    · exact (fromCoeff_of_coeff_eq_self f).symm
    · apply Finset.sum_congr rfl
      intro q hq
      rw [single, fromCoeff, lifted_fromCoeff_single]
  rw [heq]
  apply le_val_mkLp_of_coeff_eq_zero
  intro q hq
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_sum]
  change WittVector.teichmuller p (f.coeff q) - _ = 0
  rw [sub_eq_zero]
  by_cases hfq : f.coeff q = 0
  · rw [hfq, WittVector.teichmuller_zero]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    by_cases h : q = u
    · subst u
      simp [hfq]
    · rw [HahnSeries.coeff_single_of_ne h]
  · have hmem : q ∈ hfin.toFinset := by
      exact hfin.mem_toFinset.mpr ⟨hfq, hq⟩
    symm
    rw [Finset.sum_eq_single q]
    · simp
    · intro u hu hne
      exact HahnSeries.coeff_single_of_ne hne.symm
    · simp [hmem]

private lemma single_one_zpow (q : ℚ) (n : ℤ) :
    (single q (1 : 𝔽ᵃ_[p])) ^ n = single (n * q) 1 := by
  have hinv (r : ℚ) : (single r (1 : 𝔽ᵃ_[p]))⁻¹ = single (-r) 1 := by
    apply inv_eq_of_mul_eq_one_right
    rw [single_mul_single, add_neg_cancel, one_mul, single_zero_one]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [pAdicHahnSeries.single_pow]
  · rw [zpow_neg, zpow_natCast, pAdicHahnSeries.single_pow, one_pow, hinv]
    congr 1
    push_cast
    ring

/-- Finite truncations converge to the series, and a finite extension of `ℚ_[p]` is closed. -/
private lemma mem_of_monomials_mem_finite_extension (f : 𝕃_[p]) (T : ℕ+)
    (hT : ∀ q ∈ f.support, ((T : ℚ) * q).isInt)
    (E : IntermediateField ℚ_[p] 𝕃_[p])
    [FiniteDimensional ℚ_[p] E]
    (hE : ∀ q ∈ f.support, single q (f.coeff q) ∈ E) : f ∈ E := by
  classical
  let : NormedAlgebra ℚ_[p] 𝕃_[p] :=
    ⟨fun c x => by rw [Algebra.smul_def, norm_mul, norm_algebraMap_Qp]⟩
  have hclosed : IsClosed (E : Set 𝕃_[p]) :=
    E.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  apply hclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
    (show (p : ℝ)⁻¹ < 1 from inv_lt_one_of_one_lt₀ hp)
  let hfin := finite_support_inter_Iio_of_bounded_denominators f T hT (n : ℚ)
  refine ⟨∑ q ∈ hfin.toFinset, single q (f.coeff q), ?_, ?_⟩
  · exact E.sum_mem fun q hq => hE q (hfin.mem_toFinset.mp hq).1
  · rw [dist_eq_norm]
    apply lt_of_le_of_lt ((norm_le_iff_le_val).mpr (le_val_sub_sum_support_below f n hfin))
    simpa [Real.rpow_neg, Real.rpow_natCast, inv_pow] using hn

/-- Adjoin the common radical and the finitely many Teichmüller coefficient values.
Every monomial, and hence the limit of the finite truncations, lies in this finite extension. -/
private lemma exists_pAdicStrictPuiseux_of_bounded_denominators_finite_coeff (f : 𝕃_[p]) (T : ℕ+)
    (hT : ∀ q ∈ f.support, ((T : ℚ) * q).isInt)
    (hf : (Set.range f.coeff).Finite) : ∃ x : pAdicStrictPuiseux p, f = x := by
  classical
  let A : Subfield 𝕃_[p] := (pAdicStrictPuiseux p).map (algClEmbd p).toRingHom
  have hA : ∀ (x : pAdicStrictPuiseux p), (x : 𝕃_[p]) ∈ A := by
    intro x
    exact Subfield.mem_map.mpr ⟨x.val, x.property, (coe_coe x.val).symm⟩
  have hbase : Set.range (algebraMap ℚ_[p] 𝕃_[p]) ⊆ A := by
    rintro _ ⟨x, rfl⟩
    apply Subfield.mem_map.mpr
    refine ⟨algebraMap ℚ_[p] (PadicAlgCl p) x, ?_, (algClEmbd p).commutes x⟩
    rw [IsScalarTower.algebraMap_apply ℚ_[p] ℚᵘⁿ_[p] (PadicAlgCl p)]
    exact qpUn_toAlgCl_mem_pAdicStrictPuiseux _
  let S : Set 𝕃_[p] := insert (single (T : ℚ)⁻¹ 1) (single 0 '' Set.range f.coeff)
  have hS : S ⊆ A := by
    intro x hx
    rcases hx with rfl | ⟨a, ha, rfl⟩
    · rw [← coe_pRadical T]
      exact hA ⟨pRadical p T, pRadical_mem_pAdicStrictPuiseux T⟩
    · obtain ⟨y, hy⟩ := exists_pAdicStrictPuiseux_coe_eq_teichmuller a
      rw [← hy]
      exact hA y
  have hSfin : S.Finite := (hf.image (single 0)).insert _
  have : Finite S := hSfin.to_subtype
  let E := IntermediateField.adjoin ℚ_[p] S
  have halg : ∀ x ∈ S, IsIntegral ℚ_[p] x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subfield.mem_map.mp (hS hx)
    exact ((Algebra.IsAlgebraic.isAlgebraic a).algHom (algClEmbd p)).isIntegral
  have : FiniteDimensional ℚ_[p] E := IntermediateField.finiteDimensional_adjoin halg
  have hEA : E.toSubfield ≤ A := IntermediateField.adjoin_le_subfield _ _ hbase hS
  have hfE : f ∈ E := by
    apply mem_of_monomials_mem_finite_extension f T hT
    intro q hq
    have hr : single (T : ℚ)⁻¹ (1 : 𝔽ᵃ_[p]) ∈ E :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    have hc : single 0 (f.coeff q) ∈ E :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨_, ⟨q, rfl⟩, rfl⟩)
    have hprod := E.mul_mem (zpow_mem hr ((T : ℚ) * q).num) hc
    rw [single_one_zpow, single_mul_single, add_zero, one_mul] at hprod
    convert hprod using 1
    rw [← Rat.eq_num_of_isInt (hT q hq)]
    congr 1
    field_simp
  obtain ⟨x, hx, heq⟩ := Subfield.mem_map.mp (hEA hfE)
  exact ⟨⟨x, hx⟩, heq.symm.trans (coe_coe x).symm⟩

end Equivalence

/-- The image of the strict `p`-adic Puiseux field in `𝕃_[p]` consists exactly of the series
with bounded exponent denominators and finitely many coefficient values. This is the explicit
form `∑ [a_i] p^(i/T)` with coefficients in a finite field used in the proofs of
Propositions 4.3 and 4.4. -/
theorem exists_pAdicStrictPuiseux_iff {p : ℕ} [Fact p.Prime] (f : 𝕃_[p]) :
    (∃ x : pAdicStrictPuiseux p, f = x) ↔
      (∃ T : ℕ+, ∀ q ∈ f.support, (T * q).isInt) ∧ (Set.range f.coeff).Finite := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨bounded_denominators_of_mem_pAdicStrictPuiseux x,
      finite_range_coeff_of_qp_algebraic _ ?_⟩
    rw [coe_coe]
    exact (Algebra.IsAlgebraic.isAlgebraic x.val).algHom (algClEmbd p)
  · rintro ⟨⟨T, hT⟩, hf⟩
    exact exists_pAdicStrictPuiseux_of_bounded_denominators_finite_coeff f T hT hf

end PAdicOrderType
