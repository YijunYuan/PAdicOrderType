/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.QTRInvariance
import PAdicOrderType.Coefficients.AggregateInvariance
import PAdicOrderType.Coefficients.PrefixRescaling
import PAdicOrderType.Digits.SeparatedPlacements

/-!
# Aggregate homogeneity on separated arithmetic blocks

This file proves Lemma 3.12. QTR insertion invariance, together with the fixed prefix for
each integer index, makes every aggregate coefficient independent of the increasing block
positions. `PAdicOrderType.exists_aggregate_homogeneity` transfers this invariance
to the finite coefficient families used in the separated coefficient estimate.
-/

namespace PAdicOrderType

open DigitSeries RamifiedCoefficients CoefficientCosets TrustworthyKedlaya

variable {p : ℕ} [Fact (Nat.Prime p)]

lemma ofFinsupp_patternAt {s : ℕ} (hs : 0 < s) (start : ℕ) (a : Fin s → ℕ) :
    ofFinsupp (patternAt start a) =
      (placeAt
        (Finset.Icc (Nat.succPNat start) (Nat.succPNat (start + s - 1))) a) := by
  ext q
  change patternAt start a q.natPred = placeAt
    (Finset.Icc (Nat.succPNat start) (Nat.succPNat (start + s - 1))) a q
  have hcard : (Finset.Icc (Nat.succPNat start)
      (Nat.succPNat (start + s - 1))).card = s := by
    rw [card_Icc_succPNat (by omega)]
    omega
  by_cases hq : q ∈ Finset.Icc (Nat.succPNat start) (Nat.succPNat (start + s - 1))
  · rw [placeAt_Icc_apply_of_mem hcard a hq]
    rw [mem_Icc_succPNat] at hq
    have hi : q.natPred = start + (⟨q.natPred - start, by omega⟩ : Fin s) := by
      change q.natPred = start + (q.natPred - start)
      omega
    rw [hi, patternAt_apply]
    congr 1
    apply Fin.ext
    simp only [Nat.succPNat_coe]
    have := PNat.natPred_add_one q
    omega
  · rw [placeAt_apply_of_notMem hq]
    apply patternAt_eq_zero
    rw [mem_Icc_succPNat] at hq
    omega

/-- The zero-based pattern placement agrees with placement in consecutive
positive digit-coordinate intervals. -/
lemma ofFinsupp_arithmeticPlacement {s : ℕ} (hs : 0 < s) (lo Δ : ℕ)
    (w : List (Fin s → ℕ)) (l : List ℕ) :
    ofFinsupp (arithmeticPlacement lo Δ w l) =
      (placeList (fun j => Finset.Icc
        (Nat.succPNat (lo + Δ * j)) (Nat.succPNat (lo + Δ * j + s - 1))) w l) := by
  induction w generalizing l with
  | nil =>
      simp only [arithmeticPlacement_nil, placeList_nil]
      ext i
      rfl
  | cons a w ih =>
      cases l with
      | nil => ext i; rfl
      | cons j l =>
          ext q
          have hpat := congrArg (fun d : DigitSeries => d q) (ofFinsupp_patternAt hs (lo + Δ * j) a)
          have htail := congrArg (fun d : DigitSeries => d q) (ih l)
          change patternAt (lo + Δ * j) a q.natPred + arithmeticPlacement lo Δ w l q.natPred =
            placeAt (Finset.Icc (Nat.succPNat (lo + Δ * j))
              (Nat.succPNat (lo + Δ * j + s - 1))) a q +
              placeList (fun j => Finset.Icc (Nat.succPNat (lo + Δ * j))
                (Nat.succPNat (lo + Δ * j + s - 1))) w l q
          exact congrArg₂ (· + ·) hpat htail

/-- QTR coefficients in each rescaled coset are independent of the chosen
increasing block indices. This is the coefficient comparison in the proof of Lemma 3.12. -/
theorem qtr_coeff_rescaled_arithmeticPlacement {a T : ℕ+} {b c : ℕ} {M N : ℕ+}
    {x : ℚ → 𝔽ᵃ_[p]} (hx : IsQTR x a b c M N)
    {h : ℕ} (hT : (T : ℕ) = (a : ℕ) * p ^ h)
    {s lo Δ : ℕ} (hlo : (M : ℕ) ≤ lo) (hΔ : s + (M : ℕ) ≤ Δ)
    (hdiv : (N : ℕ) ∣ Δ)
    (w : List (Fin s → ℕ)) (hw : ∀ a ∈ w, ∀ i, a i < p)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) (hlen : l.length = w.length) (z : ℤ) :
    x (((z : ℚ) - (ofFinsupp (arithmeticPlacement lo Δ w (List.range w.length))).norm p) /
        (T : ℚ)) =
      x (((z : ℚ) - (ofFinsupp (arithmeticPlacement lo Δ w l)).norm p) / (T : ℚ)) := by
  obtain ⟨m, pref, hpref, hpref0, hprefix⟩ := exists_prefix_rescaling (p := p) a h z
  have hTQ : (T : ℚ) = (a : ℚ) * (p : ℚ) ^ h := by exact_mod_cast hT
  rw [hTQ, ← hprefix, ← hprefix, arithmeticPlacement_shift, arithmeticPlacement_shift]
  exact qtr_arithmeticPlacement hx m (lo := lo + h) (by omega) hΔ hdiv pref hpref
    (fun i hi => hpref0 i (by omega)) w hw l hl hlen

variable {f : 𝕃_[p]} {T : ℕ+}

/-- The aggregate coefficients inherit QTR invariance on arithmetic placements: the
coefficient `A_d` of a placement of patterns does not depend on the increasing block indices
(Lemma 3.12). -/
theorem adFun_arithmeticPlacement
    (hf2 : IsRepModZ ((DigitSeries.norm p) ''
      {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ,
        ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support})
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {a : ℕ+} {b c : ℕ} {M N : ℕ+} (hx : IsQTR f.coeff a b c M N)
    {h : ℕ} (hT : (T : ℕ) = (a : ℕ) * p ^ h)
    {s lo Δ : ℕ} (hlo : (M : ℕ) ≤ lo) (hΔ : s + (M : ℕ) ≤ Δ)
    (hdiv : (N : ℕ) ∣ Δ)
    (w : List (Fin s → ℕ)) (hw : ∀ a ∈ w, ∀ i, a i < p)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) (hlen : l.length = w.length) :
    adFun hf2 (ofFinsupp (arithmeticPlacement lo Δ w (List.range w.length))) =
      adFun hf2 (ofFinsupp (arithmeticPlacement lo Δ w l)) := by
  apply adFun_congr_coeff hf2
    (ofFinsupp_isP p _ (arithmeticPlacement_lt (by omega) w hw _ List.pairwise_lt_range))
    (ofFinsupp_isP p _ (arithmeticPlacement_lt (by omega) w hw l hl))
  exact qtr_coeff_rescaled_arithmeticPlacement hx hT hlo hΔ hdiv w hw l hl hlen

private lemma coefficientFamily_adFun_apply {D : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (u : {d : DigitSeries // d.IsP p}) :
    coefficientFamily p D (adFun hf2) u = adFun hf2 u.1 := by
  classical
  by_cases hu : u.1 ∈ D <;> simp [coefficientFamily_apply, adFun, hu]

/-- All words on a separated arithmetic family have aggregate coefficients
independent of their increasing positions (Lemma 3.12). The function `γ` gives the common
values `A_w` defined after Definition 3.13. This is the homogeneity input for
the top-ray coefficient estimate. -/
theorem exists_aggregate_homogeneity
    (hf2 : IsRepModZ ((DigitSeries.norm p) ''
      {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ,
        ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support})
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {a : ℕ+} {b c : ℕ} {M N : ℕ+} (hx : IsQTR f.coeff a b c M N)
    {h : ℕ} (hT : (T : ℕ) = (a : ℕ) * p ^ h)
    {s lo Δ : ℕ} (hs : 0 < s) (hlo : (M : ℕ) ≤ lo)
    (hΔ : s + (M : ℕ) ≤ Δ) (hdiv : (N : ℕ) ∣ Δ)
    {B : ℕ → Finset ℕ+}
    (hB : ∀ j, B j = Finset.Icc (Nat.succPNat (lo + Δ * j))
      (Nat.succPNat (lo + Δ * j + s - 1))) (r : ℕ) :
    ∃ γ : List (Fin s → ℕ) → ℚᶜᵘⁿ_[p, (T : ℕ)],
      ∀ w : List (Fin s → ℕ), w.length ≤ r → (∀ e ∈ w, ∀ t, e t < p) →
        ∀ l : List ℕ, l.Pairwise (· < ·) → l.length = w.length →
          DigitCoefficients.extendMv
            (coefficientFamily p
              {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ,
                ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support}
              (adFun hf2)) (placeList B w l) = γ w := by
  classical
  have hBfun : B = fun j => Finset.Icc (Nat.succPNat (lo + Δ * j))
      (Nat.succPNat (lo + Δ * j + s - 1)) := funext hB
  subst B
  refine ⟨fun w => adFun hf2
    (ofFinsupp (arithmeticPlacement lo Δ w (List.range w.length))), ?_⟩
  intro w _ hw l hl hlen
  have hbridge := ofFinsupp_arithmeticPlacement hs lo Δ w l
  have hproper : DigitSeries.IsP ((placeList
      (fun j => Finset.Icc (Nat.succPNat (lo + Δ * j))
        (Nat.succPNat (lo + Δ * j + s - 1))) w l)) p := by
    rw [← hbridge]
    exact ofFinsupp_isP p _ (arithmeticPlacement_lt (by omega) w hw l hl)
  rw [DigitCoefficients.extendMv_apply_of_isP _ hproper,
    coefficientFamily_adFun_apply]
  change adFun hf2 ((placeList
      (fun j => Finset.Icc (Nat.succPNat (lo + Δ * j))
        (Nat.succPNat (lo + Δ * j + s - 1))) w l)) = _
  rw [← hbridge]
  exact (adFun_arithmeticPlacement hf2 hx hT hlo hΔ hdiv w hw l hl hlen).symm

end PAdicOrderType
