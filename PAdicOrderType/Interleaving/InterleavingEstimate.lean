/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Interleaving.InterleavingNullstellensatz
import PAdicOrderType.Interleaving.NullstellensatzValuation
import PAdicOrderType.Interleaving.InterleavingRestriction

/-!
# A uniform coefficient estimate for interleavings

This file proves Lemma 3.15. A nonzero family of words of length `r` over a
characteristic-zero valued field has an `n`-fold interleaving coefficient whose valuation is
controlled by an input coefficient and a positive integer depending only on `n` and `r`.
Restricting to the letters of a witness word makes the bound independent of the alphabet.

## Main definitions

* `PAdicOrderType.fixedInterleavingConstant`: a common denominator for certificates on
  a fixed finite alphabet.
* `PAdicOrderType.interleavingConstant`: the product of these constants over alphabet
  sizes at most `r`. Its additive p-adic valuation plays the role of the constant `C(n, r)` of
  Lemma 3.15.

## Main statements

* `PAdicOrderType.exists_interleaving_coefficient_valuation`: if an input coefficient has
  multiplicative valuation at least `γ`, some nonzero output has valuation at least
  `γ ^ n * v (interleavingConstant n r)` (Lemma 3.15).

## Implementation notes

Normalize by an input coefficient of maximum multiplicative valuation and evaluate the
universal polynomial certificates at integral coordinates. For the additive p-adic valuation,
the resulting loss is the valuation of the positive integer constant. The proof of
Lemma 3.15 instead enlarges the alphabet to exactly `r` letters; taking the product over all
alphabet sizes at most `r` has the same effect.
-/

namespace PAdicOrderType

open MvPolynomial

/-- The coordinate exponent in a chosen universal Nullstellensatz certificate. -/
noncomputable def interleavingCertificateExponent (n r k : ℕ)
    (w : InterleavingVariables k r) : ℕ :=
  (exists_interleaving_nullstellensatz_certificate k r n w).choose

/-- The rational polynomial multipliers in a chosen universal certificate. -/
noncomputable def interleavingCertificate (n r k : ℕ)
    (w : InterleavingVariables k r) :
    List (Fin k) →₀ MvPolynomial (InterleavingVariables k r) ℚ :=
  (exists_interleaving_nullstellensatz_certificate k r n w).choose_spec.choose

lemma interleavingCertificate_spec (n r k : ℕ) (w : InterleavingVariables k r) :
    (interleavingCertificate n r k w).sum
      (fun z q => q * interleavingPower _ (universalInterleavingInput k r) n z) =
        X w ^ interleavingCertificateExponent n r k w :=
  (exists_interleaving_nullstellensatz_certificate k r n w).choose_spec.choose_spec

/-- A common denominator for all coordinate certificates on a fixed finite alphabet: the
integer `D` of (3.12) for that alphabet. -/
noncomputable def fixedInterleavingConstant (n r k : ℕ) : ℕ :=
  certificateDenominator (interleavingCertificate n r k)

lemma fixedInterleavingConstant_pos (n r k : ℕ) : 0 < fixedInterleavingConstant n r k :=
  certificateDenominator_pos _

section FixedAlphabet

variable {K Γ₀ : Type*} [Field K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- Lemma 3.15 on a fixed alphabet: an input coefficient of multiplicative valuation at least
`γ` gives a nonzero `n`-fold interleaving coefficient of valuation at least
`γ ^ n * v (fixedInterleavingConstant n r k)`. Normalize by a coefficient of maximum
valuation and apply the universal polynomial certificate. -/
theorem exists_fixed_interleaving_coefficient_valuation (v : Valuation K Γ₀)
    {k r : ℕ} {G : List (Fin k) →₀ K} (hlen : ∀ w ∈ G.support, w.length = r)
    {γ : Γ₀} (hγ : ∃ w ∈ G.support, γ ≤ v (G w)) (n : ℕ) :
    ∃ z : List (Fin k), z.length = n * r ∧ (interleavingPower K G n) z ≠ 0 ∧
      γ ^ n * v (fixedInterleavingConstant n r k : K) ≤
        v ((interleavingPower K G n) z) := by
  classical
  obtain ⟨w₀, hw₀, hγ⟩ := hγ
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image G.support (fun u => v (G u)) ⟨w₀, hw₀⟩
  let a := G w
  have ha : a ≠ 0 := Finsupp.mem_support_iff.mp hw
  have hva : v a ≠ 0 := (map_ne_zero v).mpr ha
  have hγa : γ ≤ v a := hγ.trans (hmax w₀ hw₀)
  let x : InterleavingVariables k r → K := fun u => a⁻¹ * G u.val
  have hx : ∀ u, v (x u) ≤ 1 := by
    intro u
    have hu : v (G u.val) ≤ v a := by
      by_cases hu : u.val ∈ G.support
      · exact hmax _ hu
      · rw [Finsupp.notMem_support_iff.mp hu, map_zero]
        exact zero_le
    change v (a⁻¹ * G u.val) ≤ 1
    rw [map_mul, map_inv₀]
    calc
      _ ≤ (v a)⁻¹ * v a := mul_le_mul' le_rfl hu
      _ = 1 := inv_mul_cancel₀ hva
  have hunit : ∃ u, x u = 1 := by
    refine ⟨⟨w, hlen w hw⟩, ?_⟩
    exact inv_mul_cancel₀ ha
  have hnormalized :
      (universalInterleavingInput k r).mapRange (aeval (R := ℚ) x).toRingHom (map_zero _) =
        a⁻¹ • G := by
    ext u
    change (aeval x) (universalInterleavingInput k r u) = a⁻¹ * G u
    rw [universalInterleavingInput_aeval]
    split_ifs with hu
    · rfl
    · have hG : G u = 0 := by
        by_contra hG
        exact hu (hlen u (Finsupp.mem_support_iff.mpr hG))
      simp [hG]
  obtain ⟨z, hz, hbound⟩ := certificate_valuation_bound
    (interleavingPower _ (universalInterleavingInput k r) n)
    (interleavingCertificateExponent n r k) (interleavingCertificate n r k)
    (interleavingCertificate_spec n r k) v x hx hunit
  have houtput :
      (interleavingPower _ (universalInterleavingInput k r) n z).eval₂ (Rat.castHom K) x =
        a⁻¹ ^ n * (interleavingPower K G n) z := by
    change ((interleavingPower _ (universalInterleavingInput k r) n).mapRange
      (aeval (R := ℚ) x).toRingHom (map_zero _)) z = _
    rw [interleavingPower_mapRange, hnormalized, interleavingPower_smul]
    rfl
  rw [houtput] at hz hbound
  have hz0 : (interleavingPower K G n) z ≠ 0 := right_ne_zero_of_mul hz
  refine ⟨z, length_eq_of_mem_support_pow hlen n z (Finsupp.mem_support_iff.mpr hz0), hz0, ?_⟩
  rw [map_mul, map_pow, map_inv₀] at hbound
  change v (fixedInterleavingConstant n r k : K) ≤ _ at hbound
  calc
    γ ^ n * v (fixedInterleavingConstant n r k : K) ≤
        v a ^ n * v (fixedInterleavingConstant n r k : K) :=
      mul_le_mul' (pow_le_pow_left' hγa n) le_rfl
    _ ≤ v a ^ n * ((v a)⁻¹ ^ n * v ((interleavingPower K G n) z)) :=
      mul_le_mul' le_rfl hbound
    _ = _ := by rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hva, one_pow, one_mul]

end FixedAlphabet

/-- One positive integer works for every alphabet: restrict to the at most `r`
letters of a witness word and combine the constants for the possible alphabet sizes. Its
additive p-adic valuation plays the role of the constant `C(n, r)` of Lemma 3.15. -/
noncomputable def interleavingConstant (n r : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (r + 1), fixedInterleavingConstant n r k

lemma interleavingConstant_pos (n r : ℕ) :
    0 < interleavingConstant n r := by
  apply Finset.prod_pos
  exact fun k _ => fixedInterleavingConstant_pos n r k

private lemma interleavingConstant_valuation_le {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (n r k : ℕ) (hk : k ≤ r) :
    v (interleavingConstant n r : K) ≤ v (fixedInterleavingConstant n r k : K) := by
  have hdiv : fixedInterleavingConstant n r k ∣ interleavingConstant n r :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
  obtain ⟨d, hd⟩ := hdiv
  rw [hd, Nat.cast_mul, map_mul]
  simpa using mul_le_mul' (le_refl (v (fixedInterleavingConstant n r k : K)))
    (valuation_nat_le_one v d)

/-- **Uniform interleaving estimate** (Lemma 3.15): for a nonzero coefficient family on words of
length `r > 0`, an input valuation bound `γ` yields a nonzero `n`-fold interleaving
coefficient of multiplicative valuation at least `γ ^ n * v (interleavingConstant n r)`.
The positive integer constant depends only on `n` and `r`, independently of the alphabet. -/
theorem exists_interleaving_coefficient_valuation {K Γ₀ L : Type*} [Field K] [CharZero K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [LinearOrder L] [DecidableEq L]
    {G : List L →₀ K} {r : ℕ} (_hr : 0 < r)
    (hlen : ∀ w ∈ G.support, w.length = r)
    {γ : Γ₀} (hγ : ∃ w ∈ G.support, γ ≤ v (G w)) (n : ℕ) :
    ∃ z : List L, z.length = n * r ∧ (interleavingPower K G n) z ≠ 0 ∧
      γ ^ n * v (interleavingConstant n r : K) ≤ v ((interleavingPower K G n) z) := by
  classical
  obtain ⟨w, hw, hγw⟩ := hγ
  obtain ⟨k, hk, e, w', hw'⟩ := exists_finAlphabet w
  have hkr : k ≤ r := hk.trans_eq (hlen w hw)
  let F := restrictAlphabet e G
  have hFlen : ∀ z ∈ F.support, z.length = r := by
    intro z hz
    have hne : F z ≠ 0 := Finsupp.mem_support_iff.mp hz
    change G (z.map e) ≠ 0 at hne
    have hmem : z.map e ∈ G.support := Finsupp.mem_support_iff.mpr hne
    simpa only [List.length_map] using hlen (z.map e) hmem
  have hFw : w' ∈ F.support := by
    apply Finsupp.mem_support_iff.mpr
    change G (w'.map e) ≠ 0
    rw [hw']
    exact Finsupp.mem_support_iff.mp hw
  have hγ' : γ ≤ v (F w') := by
    simpa only [F, restrictAlphabet, Finsupp.comapDomain_apply, hw'] using hγw
  obtain ⟨z, hzlen, hzne, hzval⟩ :=
    exists_fixed_interleaving_coefficient_valuation v hFlen ⟨w', hFw, hγ'⟩ n
  have hz : interleavingPower K G n (z.map e) = interleavingPower K F n z :=
    DFunLike.congr_fun (restrictAlphabet_interleavingPower e G n) z
  refine ⟨z.map e, by simpa only [List.length_map] using hzlen, ?_, ?_⟩
  · rwa [hz]
  · rw [hz]
    exact (mul_le_mul' (le_refl (γ ^ n))
      (interleavingConstant_valuation_le v n r k hkr)).trans hzval


end PAdicOrderType
