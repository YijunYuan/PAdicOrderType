/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp

/-!
# A valuation bound from polynomial certificates

Clear the denominators in finitely many rational polynomial identities
`X_w ^ e_w = ∑ Q_wz B_z`. At a point of the valuation ring with one coordinate
equal to one, some `B_z` has multiplicative valuation at least that of the common denominator.
The denominator depends only on the identities, not on the valued field. This is the final step
of the proof of Lemma 3.15, where the common denominator is the integer `D` of (3.12).
-/

namespace PAdicOrderType

open MvPolynomial

variable {σ τ : Type*}

/-- A common denominator of all coefficients in a finite family of certificates, the integer
`D` of (3.12). -/
noncomputable def certificateDenominator [Fintype σ]
    (Q : σ → τ →₀ MvPolynomial σ ℚ) : ℕ := by
  classical
  exact ∏ w, ∏ z ∈ (Q w).support, ∏ m ∈ (Q w z).support, ((Q w z).coeff m).den

lemma certificateDenominator_pos [Fintype σ] (Q : σ → τ →₀ MvPolynomial σ ℚ) :
    0 < certificateDenominator Q := by
  classical
  unfold certificateDenominator
  exact Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ =>
    Finset.prod_pos fun _ _ => Rat.den_pos _

private lemma den_dvd_certificateDenominator [Fintype σ]
    (Q : σ → τ →₀ MvPolynomial σ ℚ) (w : σ) {z : τ} (hz : z ∈ (Q w).support)
    {m : σ →₀ ℕ} (hm : m ∈ (Q w z).support) :
    ((Q w z).coeff m).den ∣ certificateDenominator Q := by
  classical
  exact (Finset.dvd_prod_of_mem (fun m => ((Q w z).coeff m).den) hm).trans
    ((Finset.dvd_prod_of_mem (fun z => ∏ m ∈ (Q w z).support, ((Q w z).coeff m).den) hz).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ w)))

variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

omit [CharZero K] in
/-- Every natural number has multiplicative valuation at most one. -/
lemma valuation_nat_le_one (v : Valuation K Γ₀) (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_add_le ih (by simp)

omit [CharZero K] in
private lemma valuation_int_le_one (v : Valuation K Γ₀) (n : ℤ) : v (n : K) ≤ 1 := by
  cases n with
  | ofNat n => simpa using valuation_nat_le_one v n
  | negSucc n =>
    simpa only [Int.cast_negSucc, Valuation.map_neg, Nat.cast_add, Nat.cast_one] using
      valuation_nat_le_one v (n + 1)

private lemma valuation_den_mul_eval_le_one (v : Valuation K Γ₀)
    (q : MvPolynomial σ ℚ) (D : ℕ)
    (hD : ∀ m ∈ q.support, (q.coeff m).den ∣ D)
    (x : σ → K) (hx : ∀ w, v (x w) ≤ 1) :
    v ((D : K) * q.eval₂ (Rat.castHom K) x) ≤ 1 := by
  classical
  rw [eval₂_eq, Finset.mul_sum]
  apply v.map_sum_le
  intro m hm
  obtain ⟨k, hk⟩ := hD m hm
  have hc : (D : K) * ((q.coeff m : ℚ) : K) = (k : K) * ((q.coeff m).num : K) := by
    rw [hk, Nat.cast_mul, Rat.cast_def]
    have hd : ((q.coeff m).den : K) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_nz _)
    field_simp
  change v ((D : K) * (((q.coeff m : ℚ) : K) * ∏ i ∈ m.support, x i ^ m i)) ≤ 1
  rw [← mul_assoc, hc, map_mul, map_mul, map_prod]
  simp_rw [Valuation.map_pow]
  apply mul_le_one₀
    (mul_le_one₀ (valuation_nat_le_one v k) zero_le (valuation_int_le_one v _)) zero_le
  exact Finset.prod_le_one (fun _ _ => zero_le) fun i _ => pow_le_one₀ zero_le (hx i)

/-- Evaluate a finite collection of Nullstellensatz certificates at integral
coordinates, one of which is one. At least one output is nonzero with the
uniform lower multiplicative valuation bound given by the common denominator, as at the end of
the proof of Lemma 3.15. -/
theorem certificate_valuation_bound [Fintype σ]
    (B : τ → MvPolynomial σ ℚ) (e : σ → ℕ)
    (Q : σ → τ →₀ MvPolynomial σ ℚ)
    (hQ : ∀ w, (Q w).sum (fun z q => q * B z) = X w ^ e w)
    (v : Valuation K Γ₀) (x : σ → K) (hx : ∀ w, v (x w) ≤ 1)
    (hunit : ∃ w, x w = 1) :
    ∃ z, (B z).eval₂ (Rat.castHom K) x ≠ 0 ∧
      v (certificateDenominator Q : K) ≤ v ((B z).eval₂ (Rat.castHom K) x) := by
  classical
  obtain ⟨w, hw⟩ := hunit
  let D := certificateDenominator Q
  have hD : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr (certificateDenominator_pos Q).ne'
  have hvD : v (D : K) ≠ 0 := (map_ne_zero v).mpr hD
  have hid : ∑ z ∈ (Q w).support,
      ((D : K) * (Q w z).eval₂ (Rat.castHom K) x) * (B z).eval₂ (Rat.castHom K) x = D := by
    have hh := congrArg (eval₂Hom (Rat.castHom K) x) (hQ w)
    simp only [Finsupp.sum, map_sum, map_mul, map_pow, coe_eval₂Hom, eval₂_X, hw, one_pow] at hh
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hh, mul_one]
  by_contra hcon
  have hout : ∀ z, v ((B z).eval₂ (Rat.castHom K) x) < v (D : K) := by
    intro z
    by_cases hz : (B z).eval₂ (Rat.castHom K) x = 0
    · rw [hz, map_zero]
      exact zero_lt_iff.mpr hvD
    · exact lt_of_not_ge fun h => hcon ⟨z, hz, h⟩
  have hlt : v (∑ z ∈ (Q w).support,
      ((D : K) * (Q w z).eval₂ (Rat.castHom K) x) * (B z).eval₂ (Rat.castHom K) x) < v (D : K) := by
    apply v.map_sum_lt hvD
    intro z hz
    rw [map_mul]
    have hq := valuation_den_mul_eval_le_one v (Q w z) D
      (fun m hm => den_dvd_certificateDenominator Q w hz hm) x hx
    exact (mul_le_of_le_one_left' hq).trans_lt (hout z)
  rw [hid] at hlt
  exact lt_irrefl _ hlt

end PAdicOrderType
