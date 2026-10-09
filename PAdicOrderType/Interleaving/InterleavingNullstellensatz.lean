/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Interleaving.InterleavingNonvanishing
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Fintype.Vector
import Mathlib.Algebra.Algebra.Rat

/-!
# Polynomial certificates for interleaving coefficients

Assign an independent variable to each word of a fixed length over a finite alphabet.
The coefficients of its interleaving powers are universal rational polynomials, the
polynomials `Σ_z(X)` in the proof of Lemma 3.15. In
characteristic zero, a nonzero input has a nonzero interleaving power, so every common
zero of the output polynomials has all input coordinates zero.

## Main definitions

* `PAdicOrderType.InterleavingVariables`: words of length `r` over `Fin k`.
* `PAdicOrderType.universalInterleavingInput`: the word family with independent variables
  as coefficients.

## Main statements

* `PAdicOrderType.universalInterleavingPower_common_zero`: every common zero of the output
  polynomials has all coordinates zero, the claim in the proof of Lemma 3.15.
* `PAdicOrderType.exists_interleaving_nullstellensatz_certificate`: **Hilbert's Nullstellensatz**
  expresses a power of each input variable as a polynomial combination of the outputs, as in
  the certificate (3.12).

Clearing the rational denominators of these certificates supplies a uniform valuation bound.
-/

namespace PAdicOrderType


open MvPolynomial

section Naturality

variable {L R S : Type*} [DecidableEq L] [CommRing R] [CommRing S]

/-- Applying a ring homomorphism to coefficients commutes with interleaving. -/
lemma interleavingProduct_mapRange (φ : R →+* S) (f g : List L →₀ R) :
    (interleavingProduct R f g).mapRange φ φ.map_zero =
      interleavingProduct S (f.mapRange φ φ.map_zero) (g.mapRange φ φ.map_zero) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' ih ih' =>
    simp only [interleavingProduct_add_left, Finsupp.mapRange_add φ.map_add, ih, ih']
  | single u a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' =>
      simp only [interleavingProduct_add_right, Finsupp.mapRange_add φ.map_add, ih, ih']
    | single v b =>
      simp only [Finsupp.mapRange_single, interleavingProduct_single_single]
      ext w
      simp [wordShuffle_apply]

lemma interleavingPower_mapRange (φ : R →+* S) (f : List L →₀ R) (n : ℕ) :
    (interleavingPower R f n).mapRange φ φ.map_zero =
      interleavingPower S (f.mapRange φ φ.map_zero) n := by
  induction n with
  | zero => simp [interleavingPower]
  | succ n ih => simp only [interleavingPower, interleavingProduct_mapRange, ih]

lemma interleavingProduct_smul_left (a : R) (f g : List L →₀ R) :
    interleavingProduct R (a • f) g = a • interleavingProduct R f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' ih ih' => simp [smul_add, interleavingProduct_add_left, ih, ih']
  | single u b =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' =>
      rw [interleavingProduct_add_right, interleavingProduct_add_right, ih, ih', smul_add]
    | single v c => simp [interleavingProduct_single_single, smul_smul, mul_assoc]

lemma interleavingProduct_smul_right (a : R) (f g : List L →₀ R) :
    interleavingProduct R f (a • g) = a • interleavingProduct R f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' ih ih' => simp [interleavingProduct_add_left, ih, ih', smul_add]
  | single u b =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' => simp [smul_add, interleavingProduct_add_right, ih, ih']
    | single v c => simp [interleavingProduct_single_single, smul_smul, mul_left_comm]

lemma interleavingPower_smul (a : R) (f : List L →₀ R) (n : ℕ) :
    interleavingPower R (a • f) n = a ^ n • interleavingPower R f n := by
  induction n with
  | zero => simp [interleavingPower]
  | succ n ih =>
    rw [interleavingPower, ih, interleavingProduct_smul_left,
      interleavingProduct_smul_right, smul_smul, ← pow_succ, interleavingPower]

end Naturality

section Universal

variable (k r : ℕ)

/-- The finitely many words of the fixed input length. -/
abbrev InterleavingVariables := { w : List (Fin k) // w.length = r }

instance : Fintype (InterleavingVariables k r) :=
  inferInstanceAs (Fintype (List.Vector (Fin k) r))

/-- Every word of length `r` receives its own indeterminate `X_w`, so that the coefficients
of the interleaving powers are the polynomials `Σ_z(X)` of the proof of Lemma 3.15. -/
noncomputable def universalInterleavingInput :
    List (Fin k) →₀ MvPolynomial (InterleavingVariables k r) ℚ :=
  ∑ w : InterleavingVariables k r, Finsupp.single w.val (X w)

lemma universalInterleavingInput_apply (w : List (Fin k)) :
    universalInterleavingInput k r w =
      if h : w.length = r then X (⟨w, h⟩ : InterleavingVariables k r) else 0 := by
  classical
  simp only [universalInterleavingInput, Finsupp.finsetSum_apply, Finsupp.single_apply]
  by_cases h : w.length = r
  · rw [dif_pos h]
    rw [Finset.sum_eq_single (⟨w, h⟩ : InterleavingVariables k r)]
    · simp
    · intro b _ hb
      have hbw : b.val ≠ w := fun he => hb (Subtype.ext he)
      simp [hbw]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b _
    have hbw : b.val ≠ w := fun he => h (he ▸ b.2)
    simp [hbw]

variable {K : Type*} [Field K] [CharZero K]

lemma universalInterleavingInput_aeval (x : InterleavingVariables k r → K)
    (w : List (Fin k)) :
    (aeval x) (universalInterleavingInput k r w) =
      if h : w.length = r then x ⟨w, h⟩ else 0 := by
  classical
  rw [universalInterleavingInput_apply]
  split_ifs <;> simp

/-- The universal output polynomials have no nonzero common zero. This is the claim in the
proof of Lemma 3.15. -/
lemma universalInterleavingPower_common_zero (n : ℕ)
    (x : InterleavingVariables k r → K)
    (hx : ∀ z, (aeval x) (interleavingPower _ (universalInterleavingInput k r) n z) = 0) :
    x = 0 := by
  classical
  let f := (universalInterleavingInput k r).mapRange (aeval x) (map_zero _)
  have hf : ∀ w, f w = if h : w.length = r then x ⟨w, h⟩ else 0 :=
    fun w => universalInterleavingInput_aeval k r x w
  have hlen : ∀ w ∈ f.support, w.length = r := by
    intro w hw
    by_contra h
    exact Finsupp.mem_support_iff.mp hw (by rw [hf w, dif_neg h])
  have hpow : interleavingPower K f n = 0 := by
    change interleavingPower K ((universalInterleavingInput k r).mapRange
      (aeval (R := ℚ) x).toRingHom (map_zero _)) n = 0
    rw [← interleavingPower_mapRange]
    ext z
    exact hx z
  have hf0 : f = 0 := by
    by_contra h
    exact interleavingPower_ne_zero hlen h n hpow
  funext w
  have h := DFunLike.congr_fun hf0 w.val
  rw [hf, dif_pos w.2] at h
  exact h

/-- Nullstellensatz supplies a rational polynomial certificate for each coordinate: the
identity (3.12) before clearing denominators. -/
lemma exists_interleaving_nullstellensatz_certificate (n : ℕ)
    (w : InterleavingVariables k r) :
    ∃ e : ℕ, ∃ Q : List (Fin k) →₀ MvPolynomial (InterleavingVariables k r) ℚ,
      Q.sum (fun z q => q * interleavingPower _ (universalInterleavingInput k r) n z) =
        X w ^ e := by
  classical
  let B := interleavingPower _ (universalInterleavingInput k r) n
  let I := Ideal.span (Set.range B)
  have hw : X w ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℚ)]
    intro x hx
    have hx0 : x = 0 := universalInterleavingPower_common_zero k r n x fun z =>
      hx (B z) (Ideal.subset_span (Set.mem_range_self z))
    simp [hx0]
  obtain ⟨e, he⟩ := hw
  obtain ⟨Q, hQ⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp he
  exact ⟨e, Q, hQ⟩

end Universal

end PAdicOrderType
