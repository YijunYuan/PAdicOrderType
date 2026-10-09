/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.RingTheory.HahnSeries.Valuation
import PAdicOrderType.Puiseux.FiniteCoeffLaurent
import PAdicOrderType.Puiseux.PuiseuxApproximation
import PAdicOrderType.OrderType.SupportOrderType

/-!
# The shadow map and completed algebraic closures

This file formalizes Section 2.3: the shadow map (Definition 2.7) and Proposition 2.9. The
shadow map identifies the closure of the elements of `HahnSeries ℚ 𝔽ᵃ_[p]` algebraic over
`𝔽_[p]⸨X⸩` with the image of `ℂ_[p]` in the `p`-adic Hahn field `𝕃_[p]`.

Kedlaya's coefficient description (Theorem 2.8) identifies the closure of the shadows of
elements algebraic over `𝔽ᵃ_[p]⸨X⸩` with the closure of the elements algebraic over
`ℚᶜᵘⁿ_[p]`. The latter closure is the embedded field `ℂ_[p]`. Finite Laurent truncations and
continuity of roots then show that replacing `𝔽ᵃ_[p]⸨X⸩` by `𝔽_[p]⸨X⸩` preserves the
closure.

## Main definitions

* `PAdicOrderType.shadowHomeomorph`: the shadow map `Θ` of Definition 2.7 as a homeomorphism for
  the valuation topologies.

## Main statements

* `PAdicOrderType.image_shadow_closure_algebraicClosure`: the shadow map transports the completed
  relative algebraic closure of `𝔽ᵃ_[p]⸨X⸩` to that of `ℚᶜᵘⁿ_[p]`, a consequence of
  Theorem 2.8.
* `PAdicOrderType.closure_algebraicClosure_qpCUn_eq_range_ofPadicComplex`: the latter closure is
  the image of `ℂ_[p]` in `𝕃_[p]`, the first step of the proof of Proposition 2.9.
* `PAdicOrderType.closure_algebraicClosure_laurentSeries_zmod_eq_fpbar`: extending the Laurent
  coefficient field from `𝔽_[p]` to `𝔽ᵃ_[p]` preserves the completed relative algebraic closure,
  the claim in the proof of Proposition 2.9.
* `PAdicOrderType.image_shadow_closure_algebraicClosure_eq_range_ofPadicComplex`: the resulting
  identification of the completed relative algebraic closure of `𝔽_[p]⸨X⸩`
  with the image of `ℂ_[p]` (Proposition 2.9).

## Notation

`𝔽_[p]` is `ZMod p`, `𝔽ᵃ_[p]` is its algebraic closure, and `K⸨X⸩` denotes Laurent series over `K`.
The field `ℚᶜᵘⁿ_[p]` is the completion of the maximal unramified extension of `ℚ_[p]`,
`ℂ_[p]` is the completion of `PadicAlgCl p`, and `𝕃_[p]` is the `p`-adic Hahn field.

## Implementation notes

All closures are taken in the ambient Hahn fields. The valuation on `HahnSeries ℚ 𝔽ᵃ_[p]`
is installed locally. A compatible norm, `p ^ (-orderTop)`, allows the Laurent approximation
argument to use `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`.
The proof for `ℂ_[p]` uses its algebraic closedness, its closed isometric image in `𝕃_[p]`,
and density of `PadicAlgCl p` in its completion.
-/

namespace PAdicOrderType

open TrustworthyKedlaya pAdicHahnSeries

/-! ### The shadow homeomorphism -/

/-- The valuation topology on Hahn series, induced by the least exponent with
nonzero coefficient. -/
noncomputable local instance (p : ℕ) [Fact (Nat.Prime p)] :
    Valued (HahnSeries ℚ 𝔽ᵃ_[p]) (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  Valued.mk' (HahnSeries.addVal ℚ 𝔽ᵃ_[p]).toValuation

/-- A surjective map fixing zero and preserving the valuation of differences is uniformly
continuous for the valuation uniformities. -/
private lemma uniformContinuous_of_valuation_sub_eq
    {K L Γ₀ : Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [Valued L Γ₀] (f : K → L) (hf : Function.Surjective f)
    (hzero : f 0 = 0) (hval : ∀ x y : K, Valued.v (f x - f y) = Valued.v (x - y)) :
    UniformContinuous f := by
  rw [(Valued.hasBasis_uniformity K Γ₀).uniformContinuous_iff
    (Valued.hasBasis_uniformity L Γ₀)]
  intro γ _
  obtain ⟨z, hz⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (f := MonoidWithZeroHom.ofClass (Valued.v (R := L))) γ.val
  obtain ⟨a, rfl⟩ := hf z
  have hfa : Valued.v (f a) = Valued.v a := by
    simpa only [hzero, sub_zero] using hval a 0
  have ha : Valued.v.restrict a ≠ 0 := by
    intro h
    have : Valued.v.restrict (f a) = 0 := (Valuation.restrict_eq_zero_iff _).mpr
      (hfa.trans ((Valuation.restrict_eq_zero_iff _).mp h))
    exact γ.ne_zero (hz.symm.trans this)
  refine ⟨Units.mk0 (Valued.v.restrict a) ha, trivial, ?_⟩
  intro x y hxy
  change Valued.v.restrict (f y - f x) < γ.val
  rw [← hz, ← Valuation.restrict_def, Valuation.restrict_lt_iff, hval]
  rw [hfa]
  exact (Valuation.restrict_lt_iff _).mp hxy

/-- The shadow map `Θ` of Definition 2.7 as a homeomorphism from `HahnSeries ℚ 𝔽ᵃ_[p]` to
`𝕃_[p]`, with inverse `TrustworthyKedlaya.pAdicHahnSeries.coeffSeries`.

The identity `TrustworthyKedlaya.pAdicHahnSeries.val_shadow_sub` gives uniform continuity in
both directions for the valuation topologies. This is the identity
`v_t(x - y) = v_p(Θ(x) - Θ(y))` in the proof of Proposition 2.9. -/
noncomputable def shadowHomeomorph (p : ℕ) [Fact (Nat.Prime p)] :
    HahnSeries ℚ 𝔽ᵃ_[p] ≃ₜ 𝕃_[p] where
  toFun := shadow
  invFun := coeffSeries
  left_inv := coeffSeries_shadow
  right_inv := shadow_coeffSeries
  continuous_toFun := (uniformContinuous_of_valuation_sub_eq shadow
    (fun x ↦ ⟨coeffSeries x, shadow_coeffSeries x⟩) shadow_zero
    (fun x y ↦ congrArg (fun q ↦ Multiplicative.ofAdd (OrderDual.toDual q))
      (val_shadow_sub x y))).continuous
  continuous_invFun := (uniformContinuous_of_valuation_sub_eq coeffSeries
    (fun x ↦ ⟨shadow x, coeffSeries_shadow x⟩)
    (by simpa only [shadow_zero] using (coeffSeries_shadow (0 : HahnSeries ℚ 𝔽ᵃ_[p])))
    (fun x y ↦ by
      change Multiplicative.ofAdd (OrderDual.toDual ((coeffSeries x - coeffSeries y).orderTop)) =
        Multiplicative.ofAdd (OrderDual.toDual (val p (x - y)))
      congr 2
      simpa only [shadow_coeffSeries] using
        (val_shadow_sub (coeffSeries x) (coeffSeries y)).symm)).continuous

/-! ### Completed algebraic closures in the `p`-adic Hahn field -/

open LaurentSeries in
/-- The shadow map sends the closure of the elements algebraic over `𝔽ᵃ_[p]⸨X⸩` onto the closure
of the elements of `𝕃_[p]` algebraic over `ℚᶜᵘⁿ_[p]`.

Kedlaya's coefficient description (Theorem 2.8) identifies the closures of the algebraic
elements on the p-adic side and the shadows of algebraic elements on the ordinary Hahn side.
The homeomorphism `PAdicOrderType.shadowHomeomorph` commutes with taking closure. -/
theorem image_shadow_closure_algebraicClosure (p : ℕ) [Fact (Nat.Prime p)] :
    shadow '' closure (algebraicClosure (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p])).carrier =
      closure (algebraicClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  calc
    _ = closure (shadow '' (algebraicClosure (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p])).carrier) :=
      (shadowHomeomorph p).image_closure _
    _ = _ := by
      change _ = closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier
      rw [kedlaya_2017_theorem13_4 p]
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, mem_algebraicClosure_iff.mp hy, coeff_shadow y⟩
      · rintro ⟨y, hy, hcoeff⟩
        refine ⟨y, mem_algebraicClosure_iff.mpr hy, ?_⟩
        apply ext_coeff
        exact (coeff_shadow y).trans hcoeff.symm

/-- The closure of the relative algebraic closure of `ℚᶜᵘⁿ_[p]` in `𝕃_[p]` is the image of `ℂ_[p]`.

The image is closed because the embedding is isometric and `ℂ_[p]` is complete. Algebraic
closedness of `ℂ_[p]` gives one inclusion; density of `PadicAlgCl p` gives the other. This is
the first step of the proof of Proposition 2.9. -/
theorem closure_algebraicClosure_qpCUn_eq_range_ofPadicComplex
    (p : ℕ) [Fact (Nat.Prime p)] :
    closure (algebraicClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier = Set.range ((↑) : ℂ_[p] → 𝕃_[p]) := by
  apply le_antisymm
  · refine closure_minimal ?_ (isometry_coe (p := p)).isClosedEmbedding.isClosed_range
    intro x hx
    have hx' : x ∈ algebraicClosure ℂ_[p] 𝕃_[p] :=
      mem_algebraicClosure_iff.mpr ((mem_algebraicClosure_iff.mp hx).tower_top ℂ_[p])
    rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
      (algebraicClosure ℂ_[p] 𝕃_[p])] at hx'
    exact hx'
  · rintro _ ⟨z, rfl⟩
    refine UniformSpace.Completion.induction_on z
      (isClosed_closure.preimage continuous_coe) ?_
    intro a
    apply subset_closure
    rw [coe_coe]
    apply mem_algebraicClosure_iff.mpr
    exact ((Algebra.IsAlgebraic.isAlgebraic a).algHom (algClEmbd p)).tower_top ℚᶜᵘⁿ_[p]

/-! ### Approximation by algebraic elements over the prime Laurent field -/

/-- A root of a monic polynomial lies in the closure of an algebraically closed subfield if
all coefficients lie in that closure.

Approximate the polynomial by monic polynomials of the same degree over the subfield and apply
`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`. This is the continuity of roots
used in the proof of Proposition 2.9. -/
private lemma mem_closure_of_monic_of_coeff_mem_closure_of_eval_eq_zero
    {L : Type*} [NormedField L]
    (K : Subfield L) [IsAlgClosed K] {f : Polynomial L} (hf : f.Monic)
    (hc : ∀ n : ℕ, f.coeff n ∈ closure (K : Set L)) {x : L} (hx : f.eval x = 0) :
    x ∈ closure (K : Set L) := by
  let C := K.topologicalClosure
  let : Algebra K C := (Subfield.inclusion K.le_topologicalClosure).toAlgebra
  have hd : DenseRange (algebraMap K C) :=
    (denseRange_inclusion_iff K.le_topologicalClosure).mpr Set.Subset.rfl
  obtain ⟨f', hf'⟩ := (Polynomial.mem_lifts f).mp
    ((Polynomial.lifts_iff_coeff_lifts f).mpr fun n ↦ ⟨⟨f.coeff n, hc n⟩, rfl⟩ :
      f ∈ Polynomial.lifts C.subtype)
  have hmon : f'.Monic := Polynomial.monic_map_iff.mp (hf' ▸ hf)
  have hdeg : f.natDegree ≠ 0 := by
    intro h
    simp [hf.natDegree_eq_zero.mp h] at hx
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hε : 0 < (δ / max ‖x‖ 1) ^ f.natDegree / (f.natDegree + 1) := by positivity
  obtain ⟨g, hg, hgd, hgc⟩ :=
    Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd hmon hε
  have hcomp : C.subtype.comp (algebraMap K C) = K.subtype := rfl
  have hnorm (z : C) : ‖C.subtype z‖ = ‖z‖ := rfl
  have hcoeff : ∀ n, ‖(g.map K.subtype).coeff n - f.coeff n‖ <
      (δ / max ‖x‖ 1) ^ f.natDegree / (f.natDegree + 1) := by
    intro n
    rw [← hf', Polynomial.coeff_map, Polynomial.coeff_map, ← hcomp, RingHom.comp_apply,
      ← map_sub]
    rw [hnorm, hf']
    simpa only [Polynomial.coeff_map] using hgc n
  obtain ⟨y, hy, hxy⟩ := Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε hx hf
    (hg.map K.subtype) (by rw [Polynomial.natDegree_map, ← hgd, ← hf',
      Polynomial.natDegree_map]) hcoeff ((IsAlgClosed.splits g).map K.subtype)
  have hyK : y ∈ K := by
    rw [(IsAlgClosed.splits g).roots_map, Multiset.mem_map] at hy
    obtain ⟨y, _, rfl⟩ := hy
    exact y.property
  refine ⟨y, hyK, ?_⟩
  rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
    ← Real.rpow_mul (div_pos hδ (by positivity)).le, mul_inv_cancel₀] at hxy
  · simpa [dist_eq_norm, mul_assoc, div_mul_cancel₀ _ (by positivity : 0 < max ‖x‖ 1).ne']
      using hxy
  · simpa using hdeg
  · positivity

/-- The Hahn valuation has rank one via the real embedding `q ↦ p ^ (-q)`. -/
noncomputable local instance (p : ℕ) [Fact (Nat.Prime p)] :
    (Valued.v : Valuation (HahnSeries ℚ 𝔽ᵃ_[p]) (Multiplicative (WithTop ℚ)ᵒᵈ)).RankOne where
  hom' := (normHom p).comp MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := normHom_strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    refine ⟨HahnSeries.single 1 1, ?_, ?_⟩
    all_goals
      change Multiplicative.ofAdd (OrderDual.toDual
        (HahnSeries.single (1 : ℚ) (1 : 𝔽ᵃ_[p])).orderTop) ≠ _
      rw [HahnSeries.orderTop_single one_ne_zero]
      decide

/-- The norm on Hahn series compatible with the local valuation topology. -/
noncomputable local instance (p : ℕ) [Fact (Nat.Prime p)] :
    NormedField (HahnSeries ℚ 𝔽ᵃ_[p]) :=
  Valued.toNormedField _ (Multiplicative (WithTop ℚ)ᵒᵈ)

/-- The Hahn norm is `p ^ (-orderTop)`, with value zero at the zero series. -/
private lemma norm_hahnSeries_eq_expNNReal {p : ℕ} [Fact (Nat.Prime p)]
    (x : HahnSeries ℚ 𝔽ᵃ_[p]) :
    ‖x‖ = (expNNReal p x.orderTop : ℝ) := by
  rw [Valued.toNormedField.norm_def]
  change ((normHom p) (MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict x)) : ℝ) = _
  rw [Valuation.embedding_restrict]
  rfl

open LaurentSeries in
/-- Every Laurent series over `𝔽ᵃ_[p]`, viewed in the Hahn field, is in the closure of the
elements algebraic over `𝔽_[p]⸨X⸩`.

Truncations below integral exponents have finite support and hence finite coefficient range.
They are algebraic over `𝔽_[p]⸨X⸩` and converge to the original series. In the proof of
Proposition 2.9, this places `𝔽ᵃ_[p]⸨X⸩` in the completed algebraic closure of `𝔽_[p]⸨X⸩`. -/
private lemma intHahnEmbedding_mem_closure_algebraicClosure (p : ℕ) [Fact (Nat.Prime p)]
    (x : (𝔽ᵃ_[p])⸨X⸩) :
    intHahnEmbedding p x ∈
      closure (algebraicClosure (𝔽_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p])).carrier := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
    (show (p : ℝ)⁻¹ < 1 from inv_lt_one_of_one_lt₀ hp)
  let t := HahnSeries.truncLT (n : ℤ) x
  let y := intHahnEmbedding p t
  have ht : t.support.Finite := by
    apply (Set.finite_Ico x.order (n : ℤ)).subset
    intro m hm
    change m ∈ (HahnSeries.truncLT (n : ℤ) x).support at hm
    rw [HahnSeries.support_truncLT] at hm
    exact ⟨HahnSeries.order_le_of_coeff_ne_zero hm.1, hm.2⟩
  have hyfin : y.support.Finite :=
    (ht.image (fun m : ℤ ↦ (m : ℚ))).subset HahnSeries.support_embDomain_subset
  have hyint : IsIntegral (𝔽_[p])⸨X⸩ y := by
    apply isIntegral_hahn_of_support_int_div_of_finite_coeff 1
    · intro q hq
      obtain ⟨m, _, hm⟩ := HahnSeries.support_embDomain_subset hq
      exact ⟨m, by simpa using hm.symm⟩
    · apply ((hyfin.image y.coeff).insert 0).subset
      rintro a ⟨q, rfl⟩
      by_cases hq : y.coeff q = 0
      · simp [hq]
      · exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hq)
  refine ⟨y, mem_algebraicClosure_iff'.mpr hyint, ?_⟩
  have hord : (n : WithTop ℚ) ≤ (intHahnEmbedding p x - y).orderTop := by
    change (n : WithTop ℚ) ≤ (intHahnEmbedding p x - intHahnEmbedding p t).orderTop
    rw [← map_sub, HahnSeries.le_orderTop_iff_forall]
    intro q hq
    by_cases hmem : q ∈ Set.range (Int.castAddHom ℚ : ℤ →+ ℚ)
    · obtain ⟨m, rfl⟩ := hmem
      change ((m : ℚ) : WithTop ℚ) < (n : WithTop ℚ) at hq
      rw [show (intHahnEmbedding p (x - t)).coeff ((Int.castAddHom ℚ) m) =
        (x - t).coeff m from HahnSeries.embDomain_coeff, HahnSeries.coeff_sub]
      change x.coeff m - (HahnSeries.truncLT (n : ℤ) x).coeff m = 0
      rw [HahnSeries.coeff_truncLT_of_lt (show m < (n : ℤ) by exact_mod_cast hq), sub_self]
    · exact HahnSeries.embDomain_of_notMem_range hmem
  apply lt_of_le_of_lt (b := (p : ℝ)⁻¹ ^ n) ?_ hn
  rw [dist_eq_norm, norm_hahnSeries_eq_expNNReal]
  have h := (expNNReal_strictAnti (p := p)).antitone hord
  change expNNReal p (intHahnEmbedding p x - y).orderTop ≤
    expNNReal p ((n : ℚ) : WithTop ℚ) at h
  rw [expNNReal_coe] at h
  exact_mod_cast (show expNNReal p (intHahnEmbedding p x - y).orderTop ≤
      (p : NNReal)⁻¹ ^ n by
    simpa [expNNReal_coe, NNReal.rpow_neg, NNReal.rpow_natCast, inv_pow] using h)

open LaurentSeries in
/-- The relative algebraic closures of `𝔽_[p]⸨X⸩` and `𝔽ᵃ_[p]⸨X⸩` in the Hahn field have the
same topological closure. This is the claim in the proof of Proposition 2.9.

One inclusion follows by extension of scalars. For the reverse inclusion, finite Laurent
truncations approximate the coefficients, and continuity of roots approximates the algebraic
elements by elements of the algebraic closure of `𝔽_[p]⸨X⸩`. -/
theorem closure_algebraicClosure_laurentSeries_zmod_eq_fpbar
    (p : ℕ) [Fact (Nat.Prime p)] :
    closure (algebraicClosure (𝔽_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p])).carrier =
      closure (algebraicClosure (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p])).carrier := by
  let F := (𝔽_[p])⸨X⸩
  let H := HahnSeries ℚ 𝔽ᵃ_[p]
  let A := algebraicClosure F H
  -- Polynomials over the smaller Laurent field already split in the Hahn field.
  have hsplits (f : Polynomial F) : (f.map (algebraMap F H)).Splits := by
    rw [IsScalarTower.algebraMap_eq F (𝔽ᵃ_[p])⸨X⸩ H, ← Polynomial.map_map]
    exact UP.splits_map_intHahnEmbedding p _
  have : IsAlgClosure F A := IsAlgClosure.of_exists_root fun f hf hirr ↦ by
    obtain ⟨x, hx⟩ := (hsplits f).exists_eval_eq_zero
      (by
        rw [Polynomial.degree_map]
        exact Polynomial.degree_ne_of_natDegree_ne hirr.natDegree_pos.ne')
    have hx' : Polynomial.aeval x f = 0 := by
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    let x' : A := ⟨x, mem_algebraicClosure_iff'.mpr ⟨f, hf, hx'⟩⟩
    refine ⟨x', Subtype.val_injective ?_⟩
    exact (IntermediateField.aeval_coe A x' f).symm.trans hx'
  have hA : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  have : IsAlgClosed A.toSubfield := hA
  apply le_antisymm
  · apply closure_mono
    intro x hx
    exact mem_algebraicClosure_iff.mpr
      ((mem_algebraicClosure_iff.mp hx).tower_top (𝔽ᵃ_[p])⸨X⸩)
  · apply closure_minimal ?_ isClosed_closure
    intro x hx
    obtain ⟨f, hf, hfx⟩ := mem_algebraicClosure_iff'.mp hx
    apply mem_closure_of_monic_of_coeff_mem_closure_of_eval_eq_zero A.toSubfield
      (hf.map (algebraMap (𝔽ᵃ_[p])⸨X⸩ H))
    · intro n
      rw [Polynomial.coeff_map]
      exact intHahnEmbedding_mem_closure_algebraicClosure p (f.coeff n)
    · rwa [Polynomial.eval_map_algebraMap]

/-! ### The image of the completed algebraic closure under the shadow map -/

open LaurentSeries in
/-- **Proposition 2.9**: the shadow map sends the closure of the relative algebraic closure of
`𝔽_[p]⸨X⸩` in the Hahn field onto the image of `ℂ_[p]` in `𝕃_[p]`.

Together with `PAdicOrderType.shadowHomeomorph`, this identifies the two spaces
homeomorphically. -/
theorem image_shadow_closure_algebraicClosure_eq_range_ofPadicComplex
    (p : ℕ) [Fact (Nat.Prime p)] :
    shadow '' closure (algebraicClosure (𝔽_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p])).carrier =
      Set.range ((↑) : ℂ_[p] → 𝕃_[p]) := by
  rw [closure_algebraicClosure_laurentSeries_zmod_eq_fpbar p,
    image_shadow_closure_algebraicClosure p,
    closure_algebraicClosure_qpCUn_eq_range_ofPadicComplex p]

end PAdicOrderType
