/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import TrustworthyKedlaya.MainResults

/-!
# Finite-coefficient Hahn series over `𝔽_p((t))`

`fpLaurentEmbedding` extends coefficients from `𝔽_p` to its algebraic closure.
The induced algebra structures provide the scalar towers for Laurent and Hahn
series. A rational-exponent Hahn series with bounded denominators and finite
coefficient range is integral over `𝔽_p((t))`, by decomposition into residue
classes of exponents modulo the integers. This is the implication from the second to the
first assertion in the proof of Proposition 4.4.

Kedlaya's support bound also gives order type strictly below `ω^ω` for
Hahn series algebraic over `𝔽ᵃ_[p]((t))`. This is the result of Lisinski used in the proof of
Proposition 4.4, which is a quick consequence of Kedlaya's criterion (Theorem 2.6).

## Notation

`𝔽_[p]` denotes the prime field `ZMod p`.
-/

namespace PAdicOrderType

open TrustworthyKedlaya LaurentSeries

section LaurentCoeffExtension

variable (p : ℕ) [Fact (Nat.Prime p)]
@[inherit_doc] notation "𝔽_[" p "]" => ZMod p
/-- The coefficient-extension embedding `𝔽_p((t)) →+* 𝔽ᵃ_[p]((t))`, applying
`algebraMap (𝔽_[p]) 𝔽ᵃ_[p]` to every coefficient of a Laurent series. -/
noncomputable def fpLaurentEmbedding : (𝔽_[p])⸨X⸩ →+* (𝔽ᵃ_[p])⸨X⸩ where
  toFun x := x.map (algebraMap (𝔽_[p]) 𝔽ᵃ_[p])
  map_one' := HahnSeries.map_one (algebraMap (𝔽_[p]) 𝔽ᵃ_[p]).toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (algebraMap (𝔽_[p]) 𝔽ᵃ_[p]).toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero (algebraMap (𝔽_[p]) 𝔽ᵃ_[p]).toZeroHom
  map_add' _ _ := HahnSeries.map_add (algebraMap (𝔽_[p]) 𝔽ᵃ_[p]).toAddMonoidHom

/-- Coefficient extension of a Laurent series applies the scalar embedding to each
coefficient. -/
@[simp]
theorem coeff_fpLaurentEmbedding (x : (𝔽_[p])⸨X⸩) (n : ℤ) :
    (fpLaurentEmbedding p x).coeff n = algebraMap (𝔽_[p]) 𝔽ᵃ_[p] (x.coeff n) :=
  rfl

/-- The `𝔽_p((t))`-algebra structure on `𝔽ᵃ_[p]((t))` induced by `fpLaurentEmbedding`. -/
noncomputable instance : Algebra (𝔽_[p])⸨X⸩ (𝔽ᵃ_[p])⸨X⸩ :=
  (fpLaurentEmbedding p).toAlgebra

/-- The `𝔽_p((t))`-algebra structure on `𝔽ᵃ_[p]((t^ℚ))`: coefficient extension followed by the
value-group embedding `intHahnEmbedding`. -/
noncomputable instance : Algebra (𝔽_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p]) :=
  ((intHahnEmbedding p).comp (fpLaurentEmbedding p)).toAlgebra

instance : IsScalarTower (𝔽_[p])⸨X⸩ (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ 𝔽ᵃ_[p]) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end LaurentCoeffExtension

section FiniteCoeffLaurent

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- The Laurent series indicating the positions of the nonzero coefficient value `a`. -/
private noncomputable def laurentCoeffIndicator (x : LaurentSeries 𝔽ᵃ_[p]) (a : 𝔽ᵃ_[p]) :
    LaurentSeries (ZMod p) where
  coeff n := if x.coeff n = a ∧ a ≠ 0 then 1 else 0
  isPWO_support' := x.isPWO_support'.mono (by
    intro n hn hx
    change (if x.coeff n = a ∧ a ≠ 0 then (1 : ZMod p) else 0) ≠ 0 at hn
    simp [hx, eq_comm] at hn)

private lemma eq_sum_coeff_mul_laurentCoeffIndicator (x : LaurentSeries 𝔽ᵃ_[p])
    (hx : (Set.range x.coeff).Finite) :
    x = ∑ a ∈ hx.toFinset,
      HahnSeries.single 0 a * fpLaurentEmbedding p (laurentCoeffIndicator x a) := by
  classical
  apply HahnSeries.ext
  funext n
  rw [HahnSeries.coeff_sum]
  by_cases hn : x.coeff n = 0
  · rw [hn]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    rw [HahnSeries.coeff_single_mul, sub_zero, coeff_fpLaurentEmbedding]
    simp [laurentCoeffIndicator, hn, eq_comm]
  · rw [Finset.sum_eq_single (x.coeff n)]
    · rw [HahnSeries.coeff_single_mul, sub_zero, coeff_fpLaurentEmbedding]
      simp [laurentCoeffIndicator, hn]
    · intro a ha hne
      rw [HahnSeries.coeff_single_mul, sub_zero, coeff_fpLaurentEmbedding]
      simp [laurentCoeffIndicator, hne.symm]
    · intro hnot
      exact (hnot (hx.mem_toFinset.mpr (Set.mem_range_self n))).elim

attribute [-instance] HahnSeries.powerSeriesAlgebra in
private lemma isIntegral_hahn_constant (a : 𝔽ᵃ_[p]) :
    IsIntegral (LaurentSeries (ZMod p)) (HahnSeries.single (0 : ℚ) a) := by
  have := IsScalarTower.of_algebraMap_eq' (R := ZMod p) (S := 𝔽ᵃ_[p])
    (A := HahnSeries ℚ 𝔽ᵃ_[p]) (Subsingleton.elim _ _)
  have := IsScalarTower.of_algebraMap_eq' (R := ZMod p) (S := LaurentSeries (ZMod p))
    (A := HahnSeries ℚ 𝔽ᵃ_[p]) (Subsingleton.elim _ _)
  have h : IsIntegral (ZMod p) (algebraMap 𝔽ᵃ_[p] (HahnSeries ℚ 𝔽ᵃ_[p]) a) :=
    (Algebra.IsIntegral.isIntegral a).algebraMap
  convert h.tower_top (A := LaurentSeries (ZMod p)) using 1
  simp [HahnSeries.algebraMap_apply, HahnSeries.C_apply]

private lemma isIntegral_intHahnEmbedding_of_finite_coeff (x : LaurentSeries 𝔽ᵃ_[p])
    (hx : (Set.range x.coeff).Finite) :
    IsIntegral (LaurentSeries (ZMod p)) (intHahnEmbedding p x) := by
  rw [eq_sum_coeff_mul_laurentCoeffIndicator x hx, map_sum]
  apply UP.isIntegral_finset_sum
  intro a ha
  rw [map_mul]
  change IsIntegral _ (UP.intHahnEmbedding p _ * _)
  rw [UP.intHahnEmbedding_single]
  simp only [Int.cast_zero]
  exact (isIntegral_hahn_constant a).mul (isIntegral_algebraMap (x := laurentCoeffIndicator x a))

private lemma isIntegral_hahn_single_inv_natCast (T : ℕ+) :
    IsIntegral (LaurentSeries (ZMod p))
      (HahnSeries.single ((T : ℚ)⁻¹) (1 : 𝔽ᵃ_[p])) := by
  refine ⟨Polynomial.X ^ (T : ℕ) - Polynomial.C (HahnSeries.single (1 : ℤ) (1 : ZMod p)),
    Polynomial.monic_X_pow_sub_C _ T.ne_zero, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  rw [TrustworthyKedlaya.single_pow, one_pow,
    mul_inv_cancel₀ (by exact_mod_cast T.ne_zero)]
  have hemb : algebraMap (LaurentSeries (ZMod p)) (HahnSeries ℚ 𝔽ᵃ_[p])
      (HahnSeries.single (1 : ℤ) (1 : ZMod p)) = HahnSeries.single 1 1 := by
    change intHahnEmbedding p (fpLaurentEmbedding p _) = _
    have hm : fpLaurentEmbedding p (HahnSeries.single (1 : ℤ) (1 : ZMod p)) =
        HahnSeries.single 1 (1 : 𝔽ᵃ_[p]) := by
      apply HahnSeries.ext
      funext n
      by_cases h : n = 1 <;> simp [coeff_fpLaurentEmbedding, h]
    rw [hm]
    change UP.intHahnEmbedding p _ = _
    rw [UP.intHahnEmbedding_single]
    norm_num
  rw [hemb, sub_self]

/-- A Hahn series with uniformly bounded exponent denominators and finitely many coefficient
values is integral over `𝔽_p((t))`.

The residue-class decomposition follows `UP.isIntegral_hahn_of_support_int_div`.
Each Laurent factor is a finite linear combination of `𝔽_p((t))`-valued indicator
series with coefficients in `𝔽ᵃ_[p]`, so it is integral over `𝔽_p((t))`. This is the
algebraicity of `𝔽_{p^r}((t^{1/T}))` in the proof of Proposition 4.4. -/
theorem isIntegral_hahn_of_support_int_div_of_finite_coeff (n : ℕ+) {x : HahnSeries ℚ 𝔽ᵃ_[p]}
    (hsupp : ∀ s ∈ x.support, ∃ k : ℤ, s = (k : ℚ) / (n : ℚ))
    (hx : (Set.range x.coeff).Finite) : IsIntegral (LaurentSeries (ZMod p)) x := by
  classical
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.pos.ne'
  -- The residue classes of exponents modulo the integers.
  set S : ℕ → Set ℚ := fun k => {s : ℚ | ∃ m : ℤ, s = (k : ℚ) / (n : ℚ) + m} with hS
  -- The series decomposes along the residue classes.
  have hdecomp : x = ∑ k ∈ Finset.range (n : ℕ), hahnRestrict (S k) x := by
    refine HahnSeries.ext (funext fun s => ?_)
    rw [HahnSeries.coeff_sum]
    by_cases h0 : x.coeff s = 0
    · rw [h0]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hks : s ∈ S k
      · rw [coeff_hahnRestrict_of_mem x hks, h0]
      · rw [coeff_hahnRestrict_of_notMem x hks]
    · obtain ⟨j, hj⟩ := hsupp s h0
      have hnz : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.pos.ne'
      set k₀ : ℕ := (j % ((n : ℕ) : ℤ)).toNat with hk₀
      have hjmod0 : (0 : ℤ) ≤ j % ((n : ℕ) : ℤ) := Int.emod_nonneg j hnz
      have hjmodlt : j % ((n : ℕ) : ℤ) < ((n : ℕ) : ℤ) :=
        Int.emod_lt_of_pos j (by exact_mod_cast n.pos)
      have hk₀cast : ((k₀ : ℤ)) = j % ((n : ℕ) : ℤ) := Int.toNat_of_nonneg hjmod0
      have hmem : s ∈ S k₀ := by
        refine ⟨j / ((n : ℕ) : ℤ), ?_⟩
        have hdm : (k₀ : ℤ) + ((n : ℕ) : ℤ) * (j / ((n : ℕ) : ℤ)) = j := by
          rw [hk₀cast, Int.emod_def]
          ring
        have hq : (j : ℚ) = (k₀ : ℚ) + (n : ℚ) * ((j / ((n : ℕ) : ℤ) : ℤ) : ℚ) := by
          exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hdm.symm
        rw [hj, hq]
        field_simp
      have hothers : ∀ b ∈ Finset.range (n : ℕ), b ≠ k₀ →
          (hahnRestrict (S b) x).coeff s = 0 := by
        intro b hb hbne
        by_cases hbs : s ∈ S b
        · exfalso
          obtain ⟨m, hm⟩ := hbs
          rw [hj] at hm
          have hint : j = (b : ℤ) + ((n : ℕ) : ℤ) * m := by
            have h1 : (j : ℚ) = (b : ℚ) + (n : ℚ) * (m : ℚ) := by
              field_simp at hm
              linarith [hm]
            exact_mod_cast h1
          have hb' : b < (n : ℕ) := Finset.mem_range.mp hb
          have hbmod : j % ((n : ℕ) : ℤ) = (b : ℤ) := by
            rw [hint, Int.add_mul_emod_self_left]
            exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb')
          exact hbne (by omega)
        · exact coeff_hahnRestrict_of_notMem x hbs
      rw [Finset.sum_eq_single k₀ hothers
          (fun hout => absurd (Finset.mem_range.mpr (by omega)) hout),
        coeff_hahnRestrict_of_mem x hmem]
  -- Each residue-class piece is a monomial times a Laurent series.
  have hpiece : ∀ k : ℕ,
      hahnRestrict (S k) x
        = (HahnSeries.single ((n : ℚ)⁻¹) (1 : 𝔽ᵃ_[p])) ^ k
          * UP.intHahnEmbedding p (UP.intSupportedPreimage
              (HahnSeries.single (-((k : ℚ) / (n : ℚ))) 1 * hahnRestrict (S k) x)) := by
    intro k
    have hshift : ∀ s' ∈ (HahnSeries.single (-((k : ℚ) / (n : ℚ))) (1 : 𝔽ᵃ_[p])
        * hahnRestrict (S k) x).support, ∃ m : ℤ, s' = (m : ℚ) := by
      intro s' hs'
      rw [HahnSeries.mem_support, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add] at hs'
      have hmem := support_hahnRestrict_subset_set (S k) x (HahnSeries.mem_support _ _ |>.mpr hs')
      obtain ⟨m, hm⟩ := hmem
      exact ⟨m, by linarith [hm]⟩
    rw [UP.intHahnEmbedding_intSupportedPreimage hshift, TrustworthyKedlaya.single_pow,
      one_pow, ← mul_assoc,
      HahnSeries.single_mul_single, one_mul]
    have hexp : (k : ℚ) * (n : ℚ)⁻¹ + -((k : ℚ) / (n : ℚ)) = 0 := by
      rw [← div_eq_mul_inv]
      ring
    rw [hexp, HahnSeries.single_zero_one, one_mul]
  rw [hdecomp]
  apply UP.isIntegral_finset_sum
  intro k hk
  rw [hpiece k]
  apply ((isIntegral_hahn_single_inv_natCast n).pow k).mul
  apply isIntegral_intHahnEmbedding_of_finite_coeff
  apply (hx.insert 0).subset
  rintro v ⟨m, rfl⟩
  rw [UP.coeff_intSupportedPreimage, HahnSeries.coeff_single_mul, one_mul]
  by_cases hm : (m : ℚ) - -((k : ℚ) / (n : ℚ)) ∈ S k
  · rw [coeff_hahnRestrict_of_mem x hm]
    exact Set.mem_insert_of_mem 0 (Set.mem_range_self _)
  · rw [coeff_hahnRestrict_of_notMem x hm]
    exact Set.mem_insert 0 _

end FiniteCoeffLaurent

/-!
### The strict order-type bound for algebraic Hahn series

Kedlaya's algebraicity criterion (Theorem 2.6) bounds the entire support by one set
`S_{a,b,c}`. The order
types of its initial segments are uniformly below `ω^(c+2)`, so the support has
order type at most `ω^(c+2) < ω^ω`.
-/

section SupportOrderType

instance {p : ℕ} [Fact p.Prime] (f : HahnSeries ℚ 𝔽ᵃ_[p]) :
    WellFoundedLT ↥f.support :=
  f.isWF_support.wellFoundedLT

open Ordinal in
/-- An algebraic Hahn series over `𝔽ᵃ_[p]((t))` has support of order type below `ω^ω`. This is
the result of Lisinski used in the proof of Proposition 4.4. -/
theorem typeLT_support_lt_omega0_pow_omega0_of_isAlgebraic_laurentSeries {p : ℕ} [Fact p.Prime]
    (f : HahnSeries ℚ 𝔽ᵃ_[p]) (hf : IsAlgebraic (LaurentSeries 𝔽ᵃ_[p]) f) :
    typeLT f.support < omega0 ^ omega0 := by
  obtain ⟨a, b, c, hsupp, -⟩ := (kedlaya_2001a_theorem15 p f).mp hf.isIntegral
  have hbound : typeLT f.support ≤ omega0 ^ ((c : Ordinal) + 2) := by
    apply Ordinal.typeLT_set_le_of_rank
      (fun x : f.support => typein (α := f.support) (· < ·) x)
    · intro x y hxy
      exact (typein_lt_typein _).mpr hxy
    · intro x
      rw [← type_Iio_lt]
      let e : Set.Iio x → ↥(UP.Sabc p a b c ∩ Set.Iic x.val) := fun y =>
        ⟨y.val.val, hsupp y.val.property, (show y.val.val < x.val from y.property).le⟩
      exact (Ordinal.typeLT_set_le_of_strictMono e (fun _ _ h => h)).trans_lt
        (UP.typeLT_Sabc_inter_Iic_lt p a b c x.val)
  apply hbound.trans_lt
  apply (Ordinal.opow_lt_opow_iff_right one_lt_omega0).mpr
  exact_mod_cast natCast_lt_omega0 (c + 2)

end SupportOrderType

end PAdicOrderType
