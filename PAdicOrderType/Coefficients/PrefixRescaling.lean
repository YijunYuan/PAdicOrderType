/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Digits.WordGapGeometry
import TrustworthyKedlaya.Kedlaya.Digits
import Mathlib.Algebra.BigOperators.Field

/-!
# Prefixes for rescaled support cosets

Euclidean division of an integer index supplies a fixed digit prefix. Appending
an arbitrary tail then realizes the corresponding coset at scale `a p^h`. This constructs the
digit vectors `e*` and `e'` and the identity (3.10) in the proof of Lemma 3.12.
-/

namespace PAdicOrderType

open DigitSeries TrustworthyKedlaya.UP

variable {p : ℕ} [Fact (Nat.Prime p)]

lemma fracVal_mapDomain_add (d : ℕ →₀ ℕ) (h : ℕ) :
    fracVal p (Finsupp.mapDomain (fun i => i + h) d) =
      fracVal p d / (p : ℚ) ^ h := by
  classical
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  unfold fracVal
  rw [Finsupp.sum_mapDomain_index_inj (fun _ _ h => Nat.add_right_cancel h)]
  simp only [Finsupp.sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hpow : (p : ℚ) ^ (-((i + h : ℕ) + 1 : ℤ)) =
      (p : ℚ) ^ (-(i + 1 : ℤ)) / (p : ℚ) ^ h := by
    rw [div_eq_mul_inv, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp0]
    congr 1
    push_cast
    ring
  rw [hpow]
  ring

/-- An integer-indexed coset at scale `a p^h` has a fixed integral part and
`h`-digit prefix, followed by any chosen tail. This is the identity (3.10) in the proof of
Lemma 3.12. -/
theorem exists_prefix_rescaling (a : ℕ+) (h : ℕ) (l : ℤ) :
    ∃ (m : ℤ) (pref : ℕ →₀ ℕ),
      (∀ i, pref i < p) ∧
      (∀ i, h ≤ i → pref i = 0) ∧
      ∀ d : ℕ →₀ ℕ,
        qval p a m (pref + Finsupp.mapDomain (fun i => i + h) d) =
          ((l : ℚ) - (ofFinsupp d).norm p) / ((a : ℚ) * (p : ℚ) ^ h) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hPpos : (0 : ℤ) < (p : ℤ) ^ h := pow_pos (by exact_mod_cast hp.pos) _
  let C : ℕ := ((-l) % (p : ℤ) ^ h).toNat
  let m : ℤ := -((-l) / (p : ℤ) ^ h)
  have hCcast : (C : ℤ) = (-l) % (p : ℤ) ^ h :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hPpos))
  have hClt : C < p ^ h := by
    have hr := Int.emod_lt_of_pos (-l) hPpos
    rw [← hCcast] at hr
    exact_mod_cast hr
  have hdecomp : m * (p : ℤ) ^ h - C = l := by
    have hr := Int.emod_add_mul_ediv (-l) ((p : ℤ) ^ h)
    dsimp [m]
    rw [hCcast]
    nlinarith
  refine ⟨m, digitFinsupp p C h, digitFinsupp_lt p hp.pos C h, ?_, ?_⟩
  · intro i hi
    exact Finsupp.notMem_support_iff.mp fun hm =>
      (Nat.not_lt_of_ge hi) (Finset.mem_range.mp (digitFinsupp_support_subset p C h hm))
  · intro d
    have hprefix : fracVal p (digitFinsupp p C h) = (C : ℚ) / (p : ℚ) ^ h := by
      apply (eq_div_iff (pow_ne_zero _ hp0)).mpr
      exact fracVal_digitFinsupp_mul_pow p hp.one_lt hClt
    have hdecompQ : (m : ℚ) * (p : ℚ) ^ h - C = (l : ℚ) := by
      exact_mod_cast hdecomp
    change (1 / (a : ℚ)) * ((m : ℚ) - fracVal p
      (digitFinsupp p C h + Finsupp.mapDomain (fun i => i + h) d)) = _
    rw [fracVal_add, hprefix, fracVal_mapDomain_add, ofFinsupp_norm]
    change (1 / (a : ℚ)) * ((m : ℚ) -
      ((C : ℚ) / (p : ℚ) ^ h + fracVal p d / (p : ℚ) ^ h)) =
      ((l : ℚ) - fracVal p d) / ((a : ℚ) * (p : ℚ) ^ h)
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast a.ne_zero
    field_simp
    nlinarith

end PAdicOrderType
