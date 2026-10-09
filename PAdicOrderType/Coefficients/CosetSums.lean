/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import PAdicOrderType.Digits.DigitSeries
public import PAdicOrderType.Coefficients.RamifiedHahn

/-!
# Coefficient sums along support cosets

Proper digit vectors representing the scaled support modulo the integers select cosets
of exponents differing by multiples of `1/T`. Each nonempty coset has a least support
point. Summing the coefficients relative to that point gives a nonzero integral coefficient
bundle and a Hahn lift supported at the coset minima. Up to a power of `p^{1/T}`, the bundle
of the coset represented by `d` is the coefficient `A_d` of (3.2).

## Main definitions

* `PAdicOrderType.IsRepModZ`: a set of representatives modulo the integers.
* `PAdicOrderType.CoefficientCosets.Sd`: the support slice selected by a digit vector.
* `PAdicOrderType.CoefficientCosets.muQ`: the minimum of a nonempty slice.
* `PAdicOrderType.CoefficientCosets.Cs`: the convergent weighted coefficient sum of a slice.
* `PAdicOrderType.CoefficientCosets.fhat`: the Hahn series with these bundles at the slice minima.

## Main statements

* `PAdicOrderType.CoefficientCosets.Cs_tendsto`: the partial sums converge to the bundle.
* `PAdicOrderType.CoefficientCosets.Cs_diff_alg_v_le`: an explicit valuation bound on the tails.
* `PAdicOrderType.CoefficientCosets.fhat_diff_isTNullSeries`: the bundled lift and the
  coefficientwise Teichmüller lift differ by a null series.

## Implementation notes

The proof of Proposition 3.4 works with the coefficientwise Teichmüller lift `g̃`. The bundled
lift `fhat` regroups each coset into a single term. Since the two lifts differ by a null
series, they have the same weighted coset sums.
-/

@[expose] public section

namespace PAdicOrderType

open TrustworthyKedlaya RamifiedCoefficients


instance _root_.PNat.coe_neZero (T : ℕ+) : NeZero (T : ℕ) := ⟨T.ne_zero⟩

/-- `CharZero ℚᶜᵘⁿ_[p]` follows from the injective inclusion `ℚ_[p] → ℚᶜᵘⁿ_[p]`. -/
private instance _root_.instCharZeroQpCUn (p : ℕ) [Fact (Nat.Prime p)] : CharZero ℚᶜᵘⁿ_[p] :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℚ_[p] ℚᶜᵘⁿ_[p]))

/-- `IsRepModZ A B` says that `A` is a **set of representatives of `B` modulo `ℤ`**: every element
of `B` is congruent modulo `ℤ` to a unique element of `A`, and every element of `A` is congruent
modulo `ℤ` to some element of `B`. -/
def IsRepModZ (A B : Set ℚ) : Prop :=
  (
    ∀ b ∈ B, ∃! a ∈ A, (a - b).isInt
  ) ∧ (
    ∀ a ∈ A, ∃ b ∈ B, (a - b).isInt
  )

namespace CoefficientCosets

/-- The "coset slice" `f.support ∩ (-‖d‖/T + (1/T)ℤ)` for a `DigitSeries` `d`.
We use the equivalent algebraic form `(d.norm p + T·q).isInt`. For proper `d`, these are the
support points `T`-represented by `d` (Section 2.2). -/
noncomputable def Sd (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    Set ℚ :=
  f.support ∩ {q | ((d.norm p : ℚ) + (T : ℚ) * q).isInt = true}

/-- The coset slice `Sd d` is contained in the support of `f`. -/
lemma Sd_subset_support {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    Sd p f T d ⊆ f.support :=
  Set.inter_subset_left

/-- A support slice is well ordered as a subset of the support. When nonempty, it
therefore has a least element. -/
lemma Sd_isWF {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    (Sd p f T d).IsWF :=
  (support_IsPWO f).isWF.mono (Sd_subset_support f T d)

/-- Every digit representative selects a nonempty support slice. -/
lemma Sd_nonempty {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d : DigitSeries} (hd : d ∈ S) :
    (Sd p f T d).Nonempty := by
  have hmem : (d.norm p : ℚ) ∈ ((DigitSeries.norm p) '' S) :=
    ⟨d, hd, rfl⟩
  obtain ⟨b, hb_mem, hint⟩ := hf2.2 _ hmem
  obtain ⟨q, hq_supp, hq_eq⟩ := hb_mem
  refine ⟨q, hq_supp, ?_⟩
  change ((d.norm p : ℚ) + (T : ℚ) * q).isInt = true
  have h_eq : (d.norm p : ℚ) - b = (d.norm p : ℚ) + (T : ℚ) * q := by
    rw [← hq_eq]; ring
  rw [← h_eq]; exact hint

/-- The least support exponent in the nonempty coset selected by a digit representative.
It determines `v_p(A_d) = muQ d + ‖d‖ / T` in Section 3.1. -/
noncomputable def muQ {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ℚ :=
  (Sd_isWF f T d.val).min (Sd_nonempty hf2 d.property)

/-- `muQ d` — the chosen representative for `d` — lies in the support of `f`. -/
lemma muQ_mem_support {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : muQ hf2 d ∈ f.support := by
  have h := (Sd_isWF f T d.val).min_mem (Sd_nonempty hf2 d.property)
  exact Sd_subset_support f T _ h

/-- The defining residue property of `muQ d`: `‖d‖ + T · muQ d` is an integer, i.e. `muQ d` lies in
the coset `-‖d‖/T + (1/T)ℤ` selected by `d`. -/
lemma muQ_residue {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ((d.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d).isInt = true :=
  ((Sd_isWF f T d.val).min_mem (Sd_nonempty hf2 d.property)).2

/-- Distinct proper digit representatives have distinct slice minima. -/
lemma muQ_injective {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.Injective (muQ (T := T) hf2) := by
  intro d d' hmu
  have hd := muQ_residue hf2 d
  have hd' := muQ_residue hf2 d'
  have h_sub_int :
      ((d.val.norm p : ℚ) - (d'.val.norm p : ℚ)).isInt = true := by
    set a := (d.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d with ha_def
    set b := (d'.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d' with hb_def
    have h1 : (d.val.norm p : ℚ) - (d'.val.norm p : ℚ) = a - b := by
      rw [ha_def, hb_def, hmu]; ring
    rw [h1]
    have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt hd
    have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hd'
    rw [ha_eq, hb_eq]
    have : (a.num : ℚ) - (b.num : ℚ) = ((a.num - b.num : ℤ) : ℚ) := by push_cast; ring
    rw [this, Rat.isInt]; simp
  have heq : d.val = d'.val :=
    DigitSeries.eq_of_norm_sub_isInt (hS d.val d.property) (hS d'.val d'.property) h_sub_int
  exact Subtype.ext heq

/-- The set of least support exponents of the represented cosets:
the image of `PAdicOrderType.CoefficientCosets.muQ`. -/
noncomputable def Stilde {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) : Set ℚ :=
  Set.range (muQ (T := T) hf2)

/-- The set of representatives `S̃ = { muQ d | d ∈ S }` is contained in the support of `f`. -/
lemma Stilde_subset_support {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Stilde hf2 ⊆ f.support := by
  rintro q ⟨d, rfl⟩; exact muQ_mem_support hf2 d

/-- The set of representatives `S̃` is partially well-ordered (inheriting well-orderedness from the
support of `f`). -/
lemma Stilde_isPWO {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    (Stilde hf2).IsPWO :=
  (support_IsPWO f).mono (Stilde_subset_support hf2)

/-- The map sending a digit representative to its slice minimum, viewed in the set
of all slice minima. -/
noncomputable def muToStilde {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    S → ↥(Stilde hf2) :=
  fun d => ⟨muQ hf2 d, ⟨d, rfl⟩⟩

/-- The map `μ : S → S̃` is a bijection: injectivity is the rigidity of the representatives, and
surjectivity holds by construction of `S̃` as the range of `muQ`. -/
lemma muToStilde_bijective {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.Bijective (muToStilde (T := T) hf2) := by
  refine ⟨fun d d' h => ?_, ?_⟩
  · have : muQ hf2 d = muQ hf2 d' := by
      simpa [muToStilde] using congrArg Subtype.val h
    exact muQ_injective hS hf2 this
  · rintro ⟨q, ⟨d, hq_eq⟩⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    simp [muToStilde, hq_eq]

/-- The equivalence between proper digit representatives and the minima of their
support cosets. -/
noncomputable def muEquiv {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    S ≃ ↥(Stilde hf2) :=
  Equiv.ofBijective _ (muToStilde_bijective hS hf2)

/-- The `w`-th weighted Teichmüller coefficient of the coset with minimum `s`,
namely the lift of `f.coeff (s + w / T)` multiplied by the `w`-th power of the uniformizer. -/
noncomputable def Cs_term {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (w : ℕ) : ℤᶜᵘⁿ_[p,(T : ℕ)] :=
  OQpCUn_embd p T (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))) * (pInvT p T) ^ w

/-- The sum of the first `N` weighted coefficients of the coset with minimum `s`. -/
noncomputable def Cs_partial {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (N : ℕ) : ℤᶜᵘⁿ_[p,(T : ℕ)] :=
  ∑ w ∈ Finset.range N, Cs_term hf2 s w

/-- For `N ≤ N'`, the difference of partial sums
`Cs_partial s N' - Cs_partial s N` equals the explicit `Finset.Ico` sum of `Cs_term`. -/
private lemma Cs_partial_diff_eq_Ico_sum
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) {N N' : ℕ} (hN : N ≤ N') :
    Cs_partial hf2 s N' - Cs_partial hf2 s N
      = ∑ w ∈ Finset.Ico N N', Cs_term hf2 s w := by
  unfold Cs_partial
  simp only [Finset.range_eq_Ico]
  have h_split :
      ∑ w ∈ Finset.Ico 0 N', Cs_term hf2 s w =
        (∑ w ∈ Finset.Ico 0 N, Cs_term hf2 s w) +
        ∑ w ∈ Finset.Ico N N', Cs_term hf2 s w :=
    (Finset.sum_Ico_consecutive (fun w => Cs_term hf2 s w) (Nat.zero_le N) hN).symm
  rw [h_split, add_sub_cancel_left]

/-- The multiplicative valuation of the `w`-th summand is at most `ofAdd (-w)`.
The inequality includes the case of a zero coefficient. -/
private lemma algebraMap_Cs_term_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (w : ℕ) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s w))
      ≤ ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  unfold Cs_term
  rw [map_mul]
  rw [map_pow]
  rw [show (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])) (pInvT p T) = pInvTQ p T from rfl]
  rw [Valuation.map_mul]
  rw [show ((pInvTQ p T) ^ w : ℚᶜᵘⁿ_[p, (T : ℕ)]) = (pInvTQ p T) ^ (w : ℤ) from
    (zpow_natCast _ _).symm]
  rw [valued_v_pInvT_zpow]
  have h_OQ_le_one :
      Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
        (OQpCUn_embd p (T : ℕ)
          (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))))) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,(T : ℕ)])).valuation_le_one _
  calc Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
          (OQpCUn_embd p (T : ℕ)
            (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))))) *
          ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _)
      ≤ 1 * ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul' h_OQ_le_one (le_refl _)
    _ = ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) := one_mul _

/-- For `N ≤ N'`, the difference of the partial sums through `N'` and `N` has
multiplicative valuation at most `ofAdd (-N)` in the ramified fraction field. -/
private lemma Cs_partial_diff_alg_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) {N N' : ℕ} (hN : N ≤ N') :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
              (Cs_partial hf2 s N' - Cs_partial hf2 s N))
      ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  rw [Cs_partial_diff_eq_Ico_sum hf2 s hN]
  rw [map_sum]
  apply Valuation.map_sum_le
  intro w hw
  have hw_ge : N ≤ w := (Finset.mem_Ico.mp hw).1
  have h_w_term := algebraMap_Cs_term_v_le hf2 s w
  have h_le : ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_le_coe]
    apply Multiplicative.ofAdd_le.mpr
    have : (N : ℤ) ≤ (w : ℤ) := by exact_mod_cast hw_ge
    omega
  exact le_trans h_w_term h_le

/-- For `N ≤ M ≤ M'`, the difference of the partial sums through `M'` and `M` has
multiplicative valuation at most `ofAdd (-N)`. -/
private lemma algebraMap_Cs_partial_diff_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) {N M M' : ℕ} (hMM' : M ≤ M') (hNM : N ≤ M) :
    Valued.v
        (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s M')
          - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s M)) ≤
        ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  rw [← map_sub]
  refine le_trans (Cs_partial_diff_alg_v_le hf2 s hMM') ?_
  rw [WithZero.coe_le_coe]
  apply Multiplicative.ofAdd_le.mpr
  have : (N : ℤ) ≤ (M : ℤ) := by exact_mod_cast hNM
  omega

/-- The images of the coset partial sums form a Cauchy sequence in the ramified
fraction field. The valuation bound on the tails tends to zero. -/
private lemma algebraMap_Cs_partial_isCauchy
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    CauchySeq (fun N : ℕ =>
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)) := by
  rw [show CauchySeq (fun N : ℕ =>
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)) =
        Cauchy (Filter.atTop.map (fun N : ℕ =>
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))) from rfl,
      Valued.cauchy_iff]
  refine ⟨Filter.map_neBot, ?_⟩
  intro γ
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
  -- v4.31: `γ : (ValueGroup₀ Valued.v)ˣ`; bridge to a `WithZero (Multiplicative ℤ)` bound `c`.
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hγ_ne : c ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  set ε : NNReal :=
    WithZeroMulInt.toNNReal (p_ne_zero p) c with hε_def
  have hε_pos : (0 : NNReal) < ε := by
    rw [hε_def]
    exact WithZeroMulInt.toNNReal_pos (p_ne_zero p) hγ_ne
  have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹) ^ N < ε := by
    have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹) ^ n < ε :=
      htendsto.eventually (eventually_lt_nhds hε_pos)
    exact h_eventually.exists
  have h_convert : ∀ a : ℚᶜᵘⁿ_[p, (T : ℕ)],
      Valued.v a ≤
        ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) →
      Valued.v.restrict a < γ.1 := by
    intro a hbound
    rw [Valuation.restrict_lt_iff_lt_embedding, ← hc_def]
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hbound
    have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _)) =
        (p : NNReal) ^ (-(N : ℤ)) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero, WithZero.unzero_coe]
      congr 1
    rw [htoNN] at h_nnreal_le
    have h_pow_le : (p : NNReal) ^ (-(N : ℤ)) ≤ ((p : NNReal)⁻¹) ^ N := by
      rw [show (p : NNReal) ^ (-(N : ℤ)) = ((p : NNReal)⁻¹) ^ (N : ℤ) from by
        rw [zpow_neg, ← inv_zpow]]
      rw [show ((p : NNReal)⁻¹) ^ (N : ℤ) = ((p : NNReal)⁻¹) ^ N from zpow_natCast _ _]
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) < ε :=
      lt_of_le_of_lt (h_nnreal_le.trans h_pow_le) hN
    rw [hε_def] at h_combined
    exact hsm.lt_iff_lt.mp h_combined
  refine ⟨{ a | ∃ K : ℕ, N ≤ K ∧ a =
    algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K) }, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact Filter.mem_of_superset (Filter.Ici_mem_atTop N) (fun K hK => ⟨K, hK, rfl⟩)
  · intro a ha b hb
    obtain ⟨K, hK, rfl⟩ := ha
    obtain ⟨K', hK', rfl⟩ := hb
    rcases le_total K K' with hKK' | hKK'
    · exact h_convert _ (algebraMap_Cs_partial_diff_v_le hf2 s hKK' hK)
    · have hneg :
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K')
            - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K)
            = -(algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K)
                - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K')) := by
        ring
      rw [hneg, Valuation.map_neg]
      exact h_convert _ (algebraMap_Cs_partial_diff_v_le hf2 s hKK' hK')

/-- The initial term of a nonempty support coset is a Teichmüller unit, so its image
in the ramified fraction field has multiplicative valuation `1`. -/
lemma Cs_term_zero_v_eq_one
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) =
      (1 : WithZero (Multiplicative ℤ)) := by
  unfold Cs_term
  simp only [Nat.cast_zero, zero_div, add_zero, pow_zero, mul_one]
  have h_supp : s.val ∈ f.support := Stilde_subset_support hf2 s.property
  have h_coeff_ne : f.coeff s.val ≠ 0 := h_supp
  have h_teich_unit : IsUnit (WittVector.teichmuller p (f.coeff s.val)) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.teichmuller_coeff_zero]
    exact h_coeff_ne
  have h_embd_unit : IsUnit (OQpCUn_embd p (T : ℕ)
      (WittVector.teichmuller p (f.coeff s.val))) :=
    h_teich_unit.map (OQpCUn_embd p (T : ℕ))
  exact Valuation.Integers.one_of_isUnit' h_embd_unit
    (fun _ => (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,(T : ℕ)])).valuation_le_one _)

/-- The coset partial sums converge to a nonzero element of the ramified integral
coefficient ring. Completeness gives a limit, integrality follows from the closed unit ball,
and the initial Teichmüller unit prevents the limit from vanishing. -/
lemma exists_Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    ∃ c : ℤᶜᵘⁿ_[p,(T : ℕ)],
      c ≠ 0 ∧
      Filter.Tendsto
        (fun N => algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
        Filter.atTop
        (nhds (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) c)) := by
  -- Step 1: `algebraMap ∘ Cs_partial s` is Cauchy in `ℚᶜᵘⁿ_[p,T]` (helper lemma).
  have h_cauchy := algebraMap_Cs_partial_isCauchy hf2 s
  -- Step 2: take limit `y` in the complete DVF `ℚᶜᵘⁿ_[p,T]`.
  set y : ℚᶜᵘⁿ_[p, (T : ℕ)] := Filter.limUnder Filter.atTop
    (fun N : ℕ => algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
    with hy_def
  have hy_tendsto : Filter.Tendsto
      (fun N : ℕ => algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
      Filter.atTop (nhds y) := h_cauchy.tendsto_limUnder
  -- Step 3: `y` lies in the integer subring, hence in the image of `algebraMap`.
  have h_y_v_le_one : Valued.v y ≤ (1 : WithZero (Multiplicative ℤ)) := by
    have h_eventually : ∀ᶠ N : ℕ in Filter.atTop,
        Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
          (Cs_partial hf2 s N)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      apply Filter.Eventually.of_forall
      intro N
      exact (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,(T : ℕ)])).valuation_le_one _
    have h_closed : IsClosed
        { x : ℚᶜᵘⁿ_[p, (T : ℕ)] | Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) } := by
      have h := Valued.isClosed_integer (ℚᶜᵘⁿ_[p, (T : ℕ)])
      convert h using 1
      ext x
      simp [Valuation.mem_integer_iff]
    exact h_closed.mem_of_tendsto hy_tendsto h_eventually
  -- Step 4: lift `y` to `c : ℤᶜᵘⁿ_[p,T]` via `IsDiscreteValuationRing.exists_lift_of_le_one`.
  obtain ⟨c, hc_eq⟩ :
      ∃ c : ℤᶜᵘⁿ_[p,(T : ℕ)],
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) c = y :=
    Texists_lift_of_valued_le_one p (T : ℕ) h_y_v_le_one
  -- Step 5a: control the tail valuation at `N = 1` via closed-ball + tendsto.
  have h_tail_bound :
      Valued.v (y - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0))
        ≤ ((Multiplicative.ofAdd (-(1 : ℤ)) : Multiplicative ℤ) : WithZero _) := by
    set tgt : ℚᶜᵘⁿ_[p, (T : ℕ)] :=
      y - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)
      with htgt_def
    set ball : Set (ℚᶜᵘⁿ_[p, (T : ℕ)]) :=
      { x | Valued.v x ≤ ((Multiplicative.ofAdd (-(1 : ℤ)) : Multiplicative ℤ) : WithZero _) }
      with hball_def
    have h_ball_closed : IsClosed ball := by
      -- v4.31: `isClosed_closedBall` is stated via `Valued.v.restrict`; bridge through the
      -- value-group class of `pInvTQ p T` (whose valuation is `ofAdd(-1)`).
      have hbridge : ball =
          {x : ℚᶜᵘⁿ_[p, (T : ℕ)] | Valued.v.restrict x ≤ Valued.v.restrict (pInvTQ p (T : ℕ))} := by
        ext x
        rw [hball_def, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
          Valuation.restrict_le_iff_le_embedding, Valuation.embedding_restrict, valued_v_pInvT]
      rw [hbridge]
      exact Valued.isClosed_closedBall _ _
    have h_tendsto_tail :
        Filter.Tendsto
          (fun N : ℕ =>
            algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)
              - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0))
          Filter.atTop (nhds tgt) :=
      hy_tendsto.sub tendsto_const_nhds
    have h_eventually : ∀ᶠ N : ℕ in Filter.atTop,
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)
          - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0) ∈ ball := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      change Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)
            - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) ≤ _
      have h_partial_1 : Cs_partial hf2 s 1 = Cs_term hf2 s 0 := by
        simp [Cs_partial]
      rw [show algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0) =
            algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s 1)
          from by rw [h_partial_1]]
      rw [← map_sub]
      exact Cs_partial_diff_alg_v_le hf2 s hN
    exact h_ball_closed.mem_of_tendsto h_tendsto_tail h_eventually
  -- Step 5b: combined with the unit-valuation fact `Cs_term_zero_v_eq_one`, deduce
  -- `Valued.v y = 1` via the ultrametric strict-inequality lemma `Valuation.map_add_eq_of_lt_left`.
  have h_y_v_eq_one : Valued.v y = (1 : WithZero (Multiplicative ℤ)) := by
    have h_term_v_one := Cs_term_zero_v_eq_one hf2 s
    have h_ofAdd_neg_one_lt_one :
        ((Multiplicative.ofAdd (-(1 : ℤ)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [show (1 : WithZero (Multiplicative ℤ)) =
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) from rfl,
        WithZero.coe_lt_coe]
      exact Multiplicative.ofAdd_lt.mpr (by omega)
    have h_strict :
        Valued.v (y - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) <
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) := by
      rw [h_term_v_one]
      exact lt_of_le_of_lt h_tail_bound h_ofAdd_neg_one_lt_one
    have h_sum_eq := Valuation.map_add_eq_of_lt_left Valued.v h_strict
    have h_simplify :
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)
          + (y - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) = y := by
      ring
    rw [h_simplify, h_term_v_one] at h_sum_eq
    exact h_sum_eq
  -- `c ≠ 0` from `y ≠ 0` (Valued.v y = 1) and injectivity of algebraMap.
  have h_y_ne_zero : y ≠ 0 := by
    intro h_y0
    rw [h_y0, map_zero] at h_y_v_eq_one
    exact zero_ne_one h_y_v_eq_one
  have h_c_ne_zero : c ≠ 0 := by
    intro h_c0
    apply h_y_ne_zero
    rw [← hc_eq, h_c0, map_zero]
  -- Final assembly.
  refine ⟨c, h_c_ne_zero, ?_⟩
  rw [hc_eq]
  exact hy_tendsto

/-- The **coefficient bundle** of a support coset: the nonzero integral limit of its
weighted Teichmüller partial sums, normalized at its least exponent `s`. -/
noncomputable def Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : ℤᶜᵘⁿ_[p,(T : ℕ)] :=
  (exists_Cs hf2 s).choose

/-- `algebraMap (Cs_partial hf2 s N)` converges to `algebraMap (Cs hf2 s)` in
`ℚᶜᵘⁿ_[p,T]`. This is the analytical characterization of `Cs` as a Cauchy sum. -/
lemma Cs_tendsto {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    Filter.Tendsto
      (fun N => algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
      Filter.atTop
      (nhds (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s))) :=
  (exists_Cs hf2 s).choose_spec.2

/-- The coefficient function assigning each slice minimum its coefficient bundle,
and zero to every other exponent. -/
noncomputable def fhatCoeff {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (q : ℚ) : ℤᶜᵘⁿ_[p,(T : ℕ)] := by
  classical
  exact (if h : q ∈ Stilde hf2 then Cs hf2 ⟨q, h⟩ else 0)

/-- The Hahn lift supported at the least exponent of each represented coset, with
the convergent coefficient bundle of that coset as its coefficient. -/
noncomputable def fhat {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    TLiftedPAdicHahnSeries p (T : ℕ) where
  coeff := fhatCoeff hf2
  isPWO_support' := by
    apply (Stilde_isPWO hf2).mono
    intro q hq
    by_contra hq_notin
    apply hq
    show fhatCoeff hf2 q = 0
    unfold fhatCoeff
    exact dif_neg hq_notin

/-- The support of the bundled Hahn lift is contained in the set of slice minima. -/
lemma fhat_support_subset {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.support (fhat hf2).coeff ⊆ Stilde hf2 := by
  intro q hq
  by_contra hq_notin
  apply hq
  change fhatCoeff hf2 q = 0
  unfold fhatCoeff
  exact dif_neg hq_notin

/-- At a slice minimum, the bundled Hahn lift has the corresponding coset sum as
its coefficient. -/
lemma fhatCoeff_eq_Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : (fhat hf2).coeff s.val = Cs hf2 s := by
  change fhatCoeff hf2 s.val = _
  unfold fhatCoeff
  exact dif_pos s.property

/-- An integer cast to `ℚ` has `Rat.isInt = true`. -/
lemma isInt_intCast' (k : ℤ) : ((k : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- A natural cast to `ℚ` has `Rat.isInt = true`. -/
lemma isInt_natCast' (k : ℕ) : ((k : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- `Rat.isInt` is closed under addition. -/
lemma isInt_add' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a + b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) + (b.num : ℚ) = (((a.num + b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- `Rat.isInt` is closed under subtraction. -/
lemma isInt_sub' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a - b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) - (b.num : ℚ) = (((a.num - b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- Every support exponent lies in the coset of some digit representative. -/
private lemma exists_d_for_support
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_supp : q ∈ f.support) :
    ∃ d : S, ((d.val.norm p : ℚ) + (T : ℚ) * q).isInt = true := by
  have hb_mem : (-1 * (T : ℚ) * q) ∈
      ({x | ∃ q' ∈ f.support, -1 * (T : ℚ) * q' = x} : Set ℚ) :=
    ⟨q, hq_supp, rfl⟩
  obtain ⟨a, ⟨ha_mem, hint⟩, _⟩ := hf2.1 _ hb_mem
  obtain ⟨d, hd_in_S, hd_eq⟩ := ha_mem
  refine ⟨⟨d, hd_in_S⟩, ?_⟩
  have h_eq : (a : ℚ) - (-1 * (T : ℚ) * q) = (d.norm p : ℚ) + (T : ℚ) * q := by
    rw [← hd_eq]; ring
  rw [← h_eq]
  exact hint

/-- Every support exponent has a unique expression `s + w / T`, where `s` is a
slice minimum and `w` is a natural number. Minimality makes the difference nonnegative;
uniqueness of the residue representative determines `s` and then `w`. -/
private lemma Stilde_unique_decomposition
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_supp : q ∈ f.support) :
    ∃! sw : ↥(Stilde hf2) × ℕ, q = sw.1.val + (sw.2 : ℚ) / (T : ℚ) := by
  classical
  have hT_pos : (0 : ℚ) < (T : ℕ) := by exact_mod_cast T.pos
  have hT_ne : ((T : ℕ) : ℚ) ≠ 0 := ne_of_gt hT_pos
  -- Existence
  obtain ⟨d, hd_int⟩ := exists_d_for_support hf2 hq_supp
  have hq_in_Sd : q ∈ Sd p f T d.val := ⟨hq_supp, hd_int⟩
  set s := muQ hf2 d with hs_def
  have hs_residue : ((d.val.norm p : ℚ) + (T : ℚ) * s).isInt = true :=
    muQ_residue hf2 d
  have hs_le_q : s ≤ q := (Sd_isWF f T d.val).min_le (Sd_nonempty hf2 d.property) hq_in_Sd
  -- Compute T·(q - s) ∈ ℕ.
  have h_diff_isInt : ((T : ℚ) * (q - s)).isInt = true := by
    have h1 : ((d.val.norm p : ℚ) + (T : ℚ) * q
              - ((d.val.norm p : ℚ) + (T : ℚ) * s)).isInt = true :=
      isInt_sub' hd_int hs_residue
    have h_eq : (d.val.norm p : ℚ) + (T : ℚ) * q
                - ((d.val.norm p : ℚ) + (T : ℚ) * s)
              = (T : ℚ) * (q - s) := by ring
    rw [← h_eq]; exact h1
  have h_diff_nonneg : 0 ≤ (T : ℚ) * (q - s) :=
    mul_nonneg hT_pos.le (sub_nonneg.mpr hs_le_q)
  -- Extract the natural number.
  set wq_int := ((T : ℚ) * (q - s)).num with hwq_def
  have h_T_eq_num : ((T : ℚ) * (q - s)) = (wq_int : ℚ) :=
    Rat.eq_num_of_isInt h_diff_isInt
  have hwq_nonneg : 0 ≤ wq_int := by
    have : (0 : ℚ) ≤ (wq_int : ℚ) := h_T_eq_num ▸ h_diff_nonneg
    exact_mod_cast this
  set wq := wq_int.toNat with hwq_nat_def
  have hwq_int_eq : (wq : ℤ) = wq_int := Int.toNat_of_nonneg hwq_nonneg
  have hwq_eq : ((T : ℚ) * (q - s)) = (wq : ℚ) := by
    rw [h_T_eq_num, ← hwq_int_eq]; push_cast; rfl
  -- Therefore q = s + wq/T.
  have h_q_decomp : q = s + (wq : ℚ) / (T : ℚ) := by
    have hqs : (q - s) = (wq : ℚ) / (T : ℚ) := by
      field_simp; linarith [hwq_eq]
    linarith
  -- Package as the existence witness.
  refine ⟨((⟨s, ⟨d, rfl⟩⟩ : ↥(Stilde hf2)), wq), h_q_decomp, ?_⟩
  rintro ⟨s', w'⟩ h_eq
  -- s' ∈ Stilde, so s' = muQ hf2 d' for some d'.
  obtain ⟨d', hd'_eq⟩ := s'.property
  -- show s' = s (equivalently s'.val = muQ hf2 d), then w' = wq.
  have hs'_le_q : (s'.val : ℚ) ≤ q := by
    rw [h_eq]
    have : (0 : ℚ) ≤ (w' : ℚ) / (T : ℚ) := div_nonneg (Nat.cast_nonneg _) hT_pos.le
    linarith
  have hs'_residue : ((d'.val.norm p : ℚ) + (T : ℚ) * s'.val).isInt = true := by
    rw [← hd'_eq]
    exact muQ_residue hf2 d'
  -- T·(q - s') = w' (a non-negative integer).
  have hTqs'_int : ((T : ℚ) * (q - s'.val)).isInt = true := by
    have h_id : (T : ℚ) * (q - s'.val) = (w' : ℚ) := by
      rw [h_eq]; field_simp; ring
    rw [h_id]; exact isInt_natCast' _
  -- (norm d) - (norm d') ∈ ℤ.
  have h_d'_int : ((d'.val.norm p : ℚ) + (T : ℚ) * q).isInt = true := by
    have h_eq2 : (d'.val.norm p : ℚ) + (T : ℚ) * q
              = ((d'.val.norm p : ℚ) + (T : ℚ) * s'.val) + (T : ℚ) * (q - s'.val) := by
      ring
    rw [h_eq2]
    exact isInt_add' hs'_residue hTqs'_int
  -- Apply hf2.1's uniqueness at b = -T·q.
  have hb_mem : (-1 * (T : ℚ) * q) ∈
      ({x | ∃ q' ∈ f.support, -1 * (T : ℚ) * q' = x} : Set ℚ) :=
    ⟨q, hq_supp, rfl⟩
  obtain ⟨a, ⟨_ha_mem, _hint⟩, ha_unique⟩ := hf2.1 _ hb_mem
  have hd_norm_in : ((d.val.norm p : ℚ)) ∈ DigitSeries.norm p '' S :=
    ⟨d.val, d.property, rfl⟩
  have hd'_norm_in : ((d'.val.norm p : ℚ)) ∈ DigitSeries.norm p '' S :=
    ⟨d'.val, d'.property, rfl⟩
  have h_d_check : ((d.val.norm p : ℚ) - (-1 * (T : ℚ) * q)).isInt = true := by
    have h_id : (d.val.norm p : ℚ) - (-1 * (T : ℚ) * q)
              = (d.val.norm p : ℚ) + (T : ℚ) * q := by ring
    rw [h_id]; exact hd_int
  have h_d'_check : ((d'.val.norm p : ℚ) - (-1 * (T : ℚ) * q)).isInt = true := by
    have h_id : (d'.val.norm p : ℚ) - (-1 * (T : ℚ) * q)
              = (d'.val.norm p : ℚ) + (T : ℚ) * q := by ring
    rw [h_id]; exact h_d'_int
  have hd_eq_a : (d.val.norm p : ℚ) = a :=
    ha_unique _ ⟨hd_norm_in, h_d_check⟩
  have hd'_eq_a : (d'.val.norm p : ℚ) = a :=
    ha_unique _ ⟨hd'_norm_in, h_d'_check⟩
  have h_norm_eq : (d.val.norm p : ℚ) = (d'.val.norm p : ℚ) := hd_eq_a.trans hd'_eq_a.symm
  -- Now muQ hf2 d = muQ hf2 d' because Sd depends only on d.norm p.
  have h_Sd_eq : Sd p f T d.val = Sd p f T d'.val := by
    unfold Sd
    congr 1
    ext q'
    simp only [Set.mem_ofPred_eq, h_norm_eq]
  have h_mu_eq : muQ hf2 d = muQ hf2 d' := by
    unfold muQ
    have hd_ne := Sd_nonempty hf2 d.property
    have hd'_ne := Sd_nonempty hf2 d'.property
    apply le_antisymm
    · refine (Sd_isWF f T d.val).min_le hd_ne ?_
      rw [h_Sd_eq]
      exact (Sd_isWF f T d'.val).min_mem hd'_ne
    · refine (Sd_isWF f T d'.val).min_le hd'_ne ?_
      rw [← h_Sd_eq]
      exact (Sd_isWF f T d.val).min_mem hd_ne
  have hs_s'_val : s'.val = s := by
    have h1 : s'.val = muQ hf2 d' := hd'_eq.symm
    have h2 : muQ hf2 d' = s := h_mu_eq.symm.trans hs_def.symm
    exact h1.trans h2
  -- Now show w' = wq.
  have h_w_eq : (w' : ℚ) = (wq : ℚ) := by
    have h1 : q - s = (w' : ℚ) / (T : ℚ) := by
      rw [hs_s'_val] at h_eq; linarith
    have h2 : q - s = (wq : ℚ) / (T : ℚ) := by linarith [h_q_decomp]
    have h12 : (w' : ℚ) / (T : ℚ) = (wq : ℚ) / (T : ℚ) := h1.symm.trans h2
    have hT_ne_R : (T : ℚ) ≠ 0 := hT_ne
    field_simp at h12
    exact h12
  have h_w_nat_eq : w' = wq := by exact_mod_cast h_w_eq
  have h_s_subtype_eq : s' = (⟨s, ⟨d, rfl⟩⟩ : ↥(Stilde hf2)) := by
    apply Subtype.ext
    exact hs_s'_val
  exact Prod.ext h_s_subtype_eq h_w_nat_eq

/-- If `q ∈ f.support` has decomposition `(s, w)` with `w ≥ 1`, then `q ∉ Stilde`. -/
private lemma not_Stilde_of_pos_w
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_supp : q ∈ f.support)
    {s : ↥(Stilde hf2)} {w : ℕ}
    (hq_eq : q = s.val + (w : ℚ) / (T : ℚ)) (hw_pos : w ≥ 1) :
    q ∉ Stilde hf2 := by
  intro hq_stil
  obtain ⟨_unique_sw, _, h_unique⟩ := Stilde_unique_decomposition hf2 hq_supp
  have h1 : q = q + (0 : ℕ) / (T : ℚ) := by simp
  have h_eq1 : (((⟨q, hq_stil⟩ : ↥(Stilde hf2)), (0 : ℕ)) : ↥(Stilde hf2) × ℕ)
                = _unique_sw := h_unique _ h1
  have h_eq2 : ((s, w) : ↥(Stilde hf2) × ℕ) = _unique_sw := h_unique _ hq_eq
  have h_combined : (((⟨q, hq_stil⟩ : ↥(Stilde hf2)), (0 : ℕ)) : ↥(Stilde hf2) × ℕ)
                    = (s, w) := h_eq1.trans h_eq2.symm
  have h_w_zero : w = 0 := (Prod.mk.injEq _ _ _ _).mp h_combined |>.2.symm
  omega

/-- At `s ∈ Stilde`, the diff coefficient equals `Cs hf2 s - Cs_term hf2 s 0`. -/
private lemma fhat_diff_coeff_Stilde
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff s.val
      = Cs hf2 s - Cs_term hf2 s 0 := by
  rw [HahnSeries.coeff_sub, fhatCoeff_eq_Cs hf2 s]
  -- Goal: Cs hf2 s - (fromCoeff ...).coeff s.val = Cs hf2 s - Cs_term hf2 s 0.
  -- (fromCoeff p T f.coeff h).coeff s.val = OQpCUn_embd p T (teichmuller p (f.coeff s.val))
  -- Cs_term hf2 s 0 = OQpCUn_embd p T (teich p (f.coeff (s.val + 0/T))) * (pInvT p T)^0
  --                = OQpCUn_embd p T (teich p (f.coeff s.val))
  unfold Cs_term
  have h0 : (s.val + (0 : ℕ) / (T : ℚ)) = s.val := by simp
  rw [h0, pow_zero, mul_one]
  rfl

/-- At `q ∈ f.support \ Stilde`, the diff coefficient equals
`-(OQpCUn_embd p T (teichmuller p (f.coeff q)))`. -/
private lemma fhat_diff_coeff_outside_Stilde
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_not_Stilde : q ∉ Stilde hf2) :
    (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q
      = -(OQpCUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f q))) := by
  rw [HahnSeries.coeff_sub]
  have h_fhat_zero : (fhat hf2).coeff q = 0 := by
    change fhatCoeff hf2 q = 0
    unfold fhatCoeff
    exact dif_neg hq_not_Stilde
  rw [h_fhat_zero, zero_sub]
  rfl

/-- At `q ∉ f.support`, the diff coefficient is 0. -/
private lemma fhat_diff_coeff_outside_support
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_not_supp : q ∉ f.support) :
    (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q = 0 := by
  rw [HahnSeries.coeff_sub]
  have h_f_coeff_zero : pAdicHahnSeries.coeff f q = 0 := by
    by_contra h
    exact hq_not_supp h
  have h_fhat_zero : (fhat hf2).coeff q = 0 := by
    change fhatCoeff hf2 q = 0
    unfold fhatCoeff
    by_cases hq_stil : q ∈ Stilde hf2
    · exfalso
      apply hq_not_supp
      exact Stilde_subset_support hf2 hq_stil
    · exact dif_neg hq_stil
  have h_fromCoeff_zero : (TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q = 0 := by
    change OQpCUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f q)) = 0
    rw [h_f_coeff_zero, WittVector.teichmuller_zero, map_zero]
  rw [h_fhat_zero, h_fromCoeff_zero, sub_zero]

/-- `Valued.v (algebraMap (Cs hf2 s - Cs_partial hf2 s N)) ≤ ofAdd(-N)`.
Obtained from the Cauchy bound `Cs_partial_diff_alg_v_le` by taking the limit as
`N' → ∞`, using `Cs_tendsto` plus `Valued.isClosed_closedBall`. -/
lemma Cs_diff_alg_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (N : ℕ) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
              (Cs hf2 s - Cs_partial hf2 s N))
      ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  -- algebraMap (Cs_partial s N') - algebraMap (Cs_partial s N) tends to
  -- algebraMap (Cs s) - algebraMap (Cs_partial s N) = algebraMap (Cs s - Cs_partial s N)
  -- as N' → ∞.  Eventually this value is in the closed ball; closed-ball-is-closed gives the result
  set target : ℚᶜᵘⁿ_[p, (T : ℕ)] :=
    algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s - Cs_partial hf2 s N)
    with htarget_def
  set ball : Set (ℚᶜᵘⁿ_[p, (T : ℕ)]) :=
    { x | Valued.v x ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) }
    with hball_def
  have h_ball_closed : IsClosed ball := by
    have hbridge : ball =
        {x : ℚᶜᵘⁿ_[p, (T : ℕ)] |
          Valued.v.restrict x ≤ Valued.v.restrict ((pInvTQ p (T : ℕ)) ^ (N : ℤ))} := by
      ext x
      rw [hball_def, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
        Valuation.restrict_le_iff_le_embedding, Valuation.embedding_restrict,
        valued_v_pInvT_zpow]
    rw [hbridge]
    exact Valued.isClosed_closedBall _ _
  have h_tendsto :
      Filter.Tendsto
        (fun N' : ℕ => algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
                        (Cs_partial hf2 s N' - Cs_partial hf2 s N))
        Filter.atTop (nhds target) := by
    have h_sub_tendsto :
        Filter.Tendsto
          (fun N' : ℕ => algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N')
                        - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
          Filter.atTop (nhds (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s)
                              - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
                                  (Cs_partial hf2 s N))) :=
      (Cs_tendsto hf2 s).sub tendsto_const_nhds
    have h_target_eq :
        target =
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s)
            - algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N) := by
      rw [htarget_def, map_sub]
    rw [h_target_eq]
    convert h_sub_tendsto using 1
    funext N'
    exact map_sub _ _ _
  have h_eventually : ∀ᶠ N' : ℕ in Filter.atTop,
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
        (Cs_partial hf2 s N' - Cs_partial hf2 s N) ∈ ball := by
    filter_upwards [Filter.eventually_ge_atTop N] with N' hN'
    exact Cs_partial_diff_alg_v_le hf2 s hN'
  exact h_ball_closed.mem_of_tendsto h_tendsto h_eventually

/-- On a fixed support coset, summing the difference between the bundled lift and
the Teichmüller lift through index `W` gives the coefficient bundle minus its partial sum
through `W + 1`. -/
private lemma per_s_inner_sum_eq
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (W : ℕ) :
    ∑ w ∈ Finset.range (W + 1),
        (pInvTQ p (T : ℕ)) ^ (w : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
            ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                          (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
              (s.val + (w : ℚ) / T))
      = algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
            (Cs hf2 s - Cs_partial hf2 s (W + 1)) := by
  -- Step 1: Pull algebraMap outside the sum by rewriting (pInvTQ)^w = algebraMap (pInvT)^w.
  have h_pInvTQ_eq_alg : ∀ w : ℕ, (pInvTQ p (T : ℕ)) ^ (w : ℤ) =
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) ((pInvT p (T : ℕ)) ^ w) := by
    intro w
    rw [show (pInvTQ p (T : ℕ)) ^ (w : ℤ) = (pInvTQ p (T : ℕ)) ^ w from zpow_natCast _ _, map_pow]
    rfl
  have h_step1 :
      ∑ w ∈ Finset.range (W + 1),
        (pInvTQ p (T : ℕ)) ^ (w : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
            ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                          (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
              (s.val + (w : ℚ) / T))
      = algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
          (∑ w ∈ Finset.range (W + 1),
            (pInvT p (T : ℕ)) ^ w *
              ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                            (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
                (s.val + (w : ℚ) / T))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [h_pInvTQ_eq_alg, map_mul]
  rw [h_step1]
  -- Step 2: Show the inner sum equals Cs s - Cs_partial s (W + 1) in ℤᶜᵘⁿ_[p,T].
  congr 1
  -- Split off w = 0 from the sum.
  rw [Finset.sum_range_succ' (fun w => (pInvT p (T : ℕ)) ^ w *
        ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                      (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
          (s.val + (w : ℚ) / T))) W]
  -- Now we have: ∑_{w' ∈ range W} (pInvT)^{w'+1} · diff.coeff(s.val + (w'+1)/T) + (pInvT)^0
  -- · diff.coeff(s.val)
  -- For w = 0:
  have h_w0 : (pInvT p (T : ℕ)) ^ 0 *
      ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
        (s.val + ((0 : ℕ) : ℚ) / T))
      = Cs hf2 s - Cs_term hf2 s 0 := by
    rw [pow_zero, one_mul]
    have h0 : (s.val + ((0 : ℕ) : ℚ) / T) = s.val := by simp
    rw [h0]
    exact fhat_diff_coeff_Stilde hf2 s
  rw [h_w0]
  -- For w' ∈ range W (i.e., w = w' + 1 ≥ 1):
  have h_w_ge1 : ∀ w' ∈ Finset.range W,
      (pInvT p (T : ℕ)) ^ (w' + 1) *
        ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                      (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
          (s.val + ((w' + 1 : ℕ) : ℚ) / T))
      = -(Cs_term hf2 s (w' + 1)) := by
    intro w' _
    by_cases hsupp : s.val + ((w' + 1 : ℕ) : ℚ) / T ∈ f.support
    · -- In supp. Since w'+1 ≥ 1, by not_Stilde_of_pos_w, s.val + (w'+1)/T ∉ Stilde.
      have h_not_Stilde : (s.val + ((w' + 1 : ℕ) : ℚ) / T) ∉ Stilde hf2 := by
        apply not_Stilde_of_pos_w hf2 hsupp (s := s) (w := w' + 1) rfl
        omega
      rw [fhat_diff_coeff_outside_Stilde hf2 h_not_Stilde]
      unfold Cs_term
      ring
    · -- Not in supp. diff.coeff = 0, and Cs_term s (w'+1) = 0.
      rw [fhat_diff_coeff_outside_support hf2 hsupp, mul_zero]
      have h_fc_zero : f.coeff (s.val + ((w' + 1 : ℕ) : ℚ) / T) = 0 := by
        by_contra h
        exact hsupp h
      unfold Cs_term
      rw [h_fc_zero, WittVector.teichmuller_zero, map_zero, zero_mul, neg_zero]
  rw [Finset.sum_congr rfl h_w_ge1]
  rw [Finset.sum_neg_distrib]
  unfold Cs_partial
  -- Now: -∑_{w' ∈ range W} Cs_term s (w'+1) + (Cs s - Cs_term s 0)
  --      = Cs s - ∑_{w ∈ range (W+1)} Cs_term s w
  rw [Finset.sum_range_succ' (fun w => Cs_term hf2 s w) W]
  ring

/-- Per-`s` slice valuation bound. For fixed `s ∈ Stilde hf2`, an integer
`n_s : ℤ`, and `W : ℕ`, the per-`s` slice `(pInvTQ)^{n_s} · algebraMap(Cs s - Cs_partial s (W+1))`
has valuation `≤ ofAdd(-(n_s + W + 1))`. -/
private lemma per_s_slice_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (n_s : ℤ) (W : ℕ) :
    Valued.v ((pInvTQ p (T : ℕ)) ^ n_s *
              algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
                (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-(n_s + (W : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_pInvT_zpow]
  have h_alg : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
              (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-((W + 1 : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero _) :=
    Cs_diff_alg_v_le hf2 s (W + 1)
  have h_cast : ((W + 1 : ℕ) : ℤ) = (W : ℤ) + 1 := by push_cast; ring
  rw [h_cast] at h_alg
  calc ((Multiplicative.ofAdd (-n_s : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
            (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-n_s : ℤ) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd (-((W : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul' (le_refl _) h_alg
    _ = ((Multiplicative.ofAdd (-n_s + -((W : ℤ) + 1)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.coe_mul, ← ofAdd_add]
    _ = ((Multiplicative.ofAdd (-(n_s + (W : ℤ) + 1)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
        congr 2; ring

/-- The weighted partial sum of the difference between the bundled and Teichmüller
lifts, truncated at exponent `M` on the coset of `g`, has multiplicative valuation at most
`ofAdd (-(K + 1))`, where `K = ⌊T * (M - g)⌋`.

Group terms by their slice minima. Each inner sum is a rescaled tail of a coefficient
bundle, so the tail bound and the ultrametric inequality give a common bound. -/
private lemma fhat_diff_partial_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (g : ℚ) (M : ℕ) :
    Valued.v (∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ)
                  (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)) g M),
              (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
                algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
                  ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
                    (g + (n.val : ℚ) / T))) ≤
      ((Multiplicative.ofAdd (-(⌊(T : ℚ) * ((M : ℚ) - g)⌋ + 1) : ℤ) :
        Multiplicative ℤ) : WithZero _) := by
  classical
  set diff : TLiftedPAdicHahnSeries p (T : ℕ) :=
    fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                (pAdicHahnSeries.coeff f) (support_IsPWO f) with hdiff_def
  set K : ℤ := ⌊(T : ℚ) * ((M : ℚ) - g)⌋ with hK_def
  have hT_pos : (0 : ℚ) < (T : ℕ) := by exact_mod_cast T.pos
  have hT_ne : ((T : ℕ) : ℚ) ≠ 0 := ne_of_gt hT_pos
  -- For each n ∈ TfiniteBelow.toFinset, g + n/T ∈ f.support.
  have h_n_supp : ∀ n : ℤ, n ∈ Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M) →
      g + (n : ℚ) / (T : ℕ) ∈ f.support := by
    intro n hn
    have hn_data : g + (n : ℚ) / (T : ℕ) ≤ M ∧ diff.coeff (g + (n : ℚ) / (T : ℕ)) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := TfiniteBelow p (T : ℕ) diff g M) (a := n)).mp hn
    by_contra h
    exact hn_data.2 (fhat_diff_coeff_outside_support hf2 h)
  -- For each n ∈ TfiniteBelow.toFinset, also: g + n/T ≤ M.
  have h_n_le_M : ∀ n : ℤ, n ∈ Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M) →
      g + (n : ℚ) / (T : ℕ) ≤ M := by
    intro n hn
    exact ((Set.Finite.mem_toFinset (hs := TfiniteBelow p (T : ℕ) diff g M) (a := n)).mp hn).1
  -- Define the bijection map on the attached set.
  let sw_choose : (n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M))) →
      ↥(Stilde hf2) × ℕ :=
    fun n => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose
  -- Property of sw_choose: g + n.val/T = (sw_choose n).1.val + (sw_choose n).2 / T.
  have h_sw_eq : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      g + (n.val : ℚ) / (T : ℕ) = ((sw_choose n).1).val +
                                   ((sw_choose n).2 : ℚ) / (T : ℕ) :=
    fun n => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose_spec.1
  -- Uniqueness of sw_choose.
  have h_sw_unique : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      ∀ sw', g + (n.val : ℚ) / (T : ℕ) = sw'.1.val + (sw'.2 : ℚ) / (T : ℕ) →
        sw' = sw_choose n :=
    fun n sw' h_eq => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose_spec.2
      sw' h_eq
  -- n.val = T·(s.val - g) + w (residue arithmetic).
  have h_n_decomp : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      (n.val : ℚ) = (T : ℕ) * (((sw_choose n).1).val - g) + ((sw_choose n).2 : ℚ) := by
    intro n
    have h1 := h_sw_eq n
    have h2 : (n.val : ℚ) / (T : ℕ) = (((sw_choose n).1).val - g) +
                                       ((sw_choose n).2 : ℚ) / (T : ℕ) := by linarith
    have h3 : (T : ℕ) * ((n.val : ℚ) / (T : ℕ)) =
              (T : ℕ) * ((((sw_choose n).1).val - g) + ((sw_choose n).2 : ℚ) / (T : ℕ)) := by
      rw [h2]
    rw [mul_div_cancel₀ _ hT_ne] at h3
    rw [h3]
    field_simp
  -- T·(s.val - g) is an integer for s in image.
  have h_T_sub_int : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      (T : ℕ) * (((sw_choose n).1).val - g) = (n.val - ((sw_choose n).2 : ℤ) : ℤ) := by
    intro n
    have h := h_n_decomp n
    have : (n.val : ℚ) - ((sw_choose n).2 : ℚ) = (T : ℕ) * (((sw_choose n).1).val - g) := by
      linarith
    rw [← this]; push_cast; ring
  -- Define Stilde_used: image of the s coordinate.
  set Stilde_used : Finset ↥(Stilde hf2) :=
    (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image
      (fun n => (sw_choose n).1) with hStilde_used_def
  -- For each s ∈ Stilde_used, define n_s : ℤ.
  -- n_s := T·(s.val - g).num (the integer value, which exists for s ∈ Stilde_used).
  set n_s_int : ↥(Stilde hf2) → ℤ := fun s => ((T : ℚ) * (s.val - g)).num with hn_s_def
  -- W_s : ℕ := ⌊T·(M - s.val)⌋.toNat.
  set W_s : ↥(Stilde hf2) → ℕ := fun s => ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋.toNat with hW_s_def
  -- For s ∈ Stilde_used: properties.
  have h_used_isInt : ∀ s ∈ Stilde_used,
      ((T : ℕ) * (s.val - g) : ℚ) = (n_s_int s : ℚ) := by
    intro s hs
    obtain ⟨n, hn_mem, hn_eq⟩ := Finset.mem_image.mp hs
    have h := h_T_sub_int n
    have hn_eq' : (sw_choose n).1 = s := hn_eq
    rw [hn_eq'] at h
    -- h : ↑↑T * (↑s - g) = ↑(↑n - ↑(sw_choose n).2)
    have hT_sval_Q : ((T : ℚ) * (s.val - g)) = ((n.val - ((sw_choose n).2 : ℤ) : ℤ) : ℚ) := by
      have : ((T : ℕ) : ℚ) = (T : ℚ) := rfl
      exact h
    have h_isInt : ((T : ℚ) * (s.val - g)).isInt = true := by
      rw [hT_sval_Q]; exact isInt_intCast' _
    have h_num_val := Rat.eq_num_of_isInt h_isInt
    -- h_num_val : ((T : ℚ) * (s.val - g)) = (((T : ℚ) * (s.val - g)).num : ℚ)
    change ((T : ℕ) * (s.val - g) : ℚ) = (((T : ℚ) * (s.val - g)).num : ℚ)
    calc ((T : ℕ) * (s.val - g) : ℚ)
        = ((T : ℚ) * (s.val - g)) := by ring
      _ = (((T : ℚ) * (s.val - g)).num : ℚ) := h_num_val
  -- For s ∈ Stilde_used: s.val ≤ M.
  have h_used_sval_le : ∀ s ∈ Stilde_used, (s.val : ℚ) ≤ M := by
    intro s hs
    obtain ⟨n, hn_mem, hn_eq⟩ := Finset.mem_image.mp hs
    have h_le := h_n_le_M n.val n.property
    have h_decomp := h_sw_eq n
    rw [hn_eq] at h_decomp
    have h_w_nonneg : 0 ≤ ((sw_choose n).2 : ℚ) / (T : ℕ) := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact hT_pos.le
    linarith
  -- For s ∈ Stilde_used: arithmetic identity n_s + W_s = K.
  have h_used_arith : ∀ s ∈ Stilde_used,
      n_s_int s + (W_s s : ℤ) = K := by
    intro s hs
    have h_int := h_used_isInt s hs
    have h_le := h_used_sval_le s hs
    -- W_s s = ⌊T(M - s.val)⌋.toNat
    -- For s.val ≤ M, T(M - s.val) ≥ 0, so ⌊T(M - s.val)⌋ ≥ 0, so W_s s = ⌊T(M - s.val)⌋.
    have h_TMsval_nonneg : (0 : ℚ) ≤ (T : ℕ) * ((M : ℚ) - s.val) := by
      apply mul_nonneg hT_pos.le
      linarith
    have h_floor_nonneg : 0 ≤ ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
      exact Int.floor_nonneg.mpr (by exact_mod_cast h_TMsval_nonneg)
    have h_W_s_eq : (W_s s : ℤ) = ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
      change (⌊(T : ℚ) * ((M : ℚ) - s.val)⌋.toNat : ℤ) = ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋
      exact Int.toNat_of_nonneg h_floor_nonneg
    rw [h_W_s_eq]
    -- Use n_s_plus_W_s_eq_floor style: T(M-g) = T(s.val-g) + T(M-s.val) = n_s + T(M-s.val).
    have h_eq : (T : ℚ) * ((M : ℚ) - g) = (n_s_int s : ℚ) + (T : ℚ) * ((M : ℚ) - s.val) := by
      have : (T : ℚ) * ((M : ℚ) - g) =
          (T : ℚ) * (s.val - g) + (T : ℚ) * ((M : ℚ) - s.val) := by ring
      rw [this]
      have h_int' : ((T : ℕ) * (s.val - g) : ℚ) = (n_s_int s : ℚ) := h_int
      rw [show ((T : ℚ) * (s.val - g)) = ((T : ℕ) * (s.val - g) : ℚ) from by ring]
      rw [h_int']
    rw [hK_def]
    rw [h_eq]
    have := Int.floor_intCast_add (n_s_int s) ((T : ℚ) * ((M : ℚ) - s.val))
    linarith
  -- For s ∈ Stilde_used: (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) bounds for per-s slice.
  -- Apply per_s_slice_v_le.
  have h_used_per_s_bound : ∀ s ∈ Stilde_used,
      Valued.v ((pInvTQ p (T : ℕ)) ^ (n_s_int s) *
                algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
                  (Cs hf2 s - Cs_partial hf2 s (W_s s + 1))) ≤
      ((Multiplicative.ofAdd (-(K + 1)) : Multiplicative ℤ) : WithZero _) := by
    intro s hs
    have h_arith := h_used_arith s hs
    have h_slice := per_s_slice_v_le hf2 s (n_s_int s) (W_s s)
    have h_eq : (n_s_int s + (W_s s : ℤ) + 1 : ℤ) = K + 1 := by linarith
    rw [h_eq] at h_slice
    exact h_slice
  -- Step: Show the sum identity.
  -- For each n ∈ TfiniteBelow, the term equals (pInvTQ)^{n.val} · algebraMap(diff.coeff(g + n/T))
  --   = (pInvTQ)^{n_s_int s + (sw_choose n).2} · algebraMap(diff.coeff(s.val + w/T))
  -- where s = (sw_choose n).1, w = (sw_choose n).2.
  -- F : value at a Sigma pair.
  let F : (Σ _ : ↥(Stilde hf2), ℕ) → ℚᶜᵘⁿ_[p, (T : ℕ)] := fun p_sig =>
    (pInvTQ p (T : ℕ)) ^ (n_s_int p_sig.1 + (p_sig.2 : ℤ)) *
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
        (diff.coeff (p_sig.1.val + (p_sig.2 : ℚ) / (T : ℕ)))
  -- sigma_of: the indexing function on the subtype.
  let sigma_of : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)) →
      Σ _ : ↥(Stilde hf2), ℕ :=
    fun n => ⟨(sw_choose n).1, (sw_choose n).2⟩
  -- F (sigma_of n) equals the original summand.
  have h_F_eq : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      F (sigma_of n) = (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
          (diff.coeff (g + (n.val : ℚ) / (T : ℕ))) := by
    intro n
    have hs_used : (sw_choose n).1 ∈ Stilde_used :=
      Finset.mem_image.mpr ⟨n, Finset.mem_attach _ _, rfl⟩
    have h_int := h_used_isInt _ hs_used
    have h_T_sub := h_T_sub_int n
    have h_int_cast : (n_s_int (sw_choose n).1 : ℚ) =
        ((n.val - ((sw_choose n).2 : ℤ) : ℤ) : ℚ) := by
      rw [← h_int]; exact_mod_cast h_T_sub
    have h_n_eq : n_s_int (sw_choose n).1 + ((sw_choose n).2 : ℤ) = (n.val : ℤ) := by
      have : (n_s_int (sw_choose n).1 : ℤ) = n.val - ((sw_choose n).2 : ℤ) := by
        exact_mod_cast h_int_cast
      omega
    have h_q_eq : (sw_choose n).1.val + ((sw_choose n).2 : ℚ) / (T : ℕ) =
        g + (n.val : ℚ) / (T : ℕ) := (h_sw_eq n).symm
    change (pInvTQ p (T : ℕ)) ^ (n_s_int (sw_choose n).1 + ((sw_choose n).2 : ℤ)) *
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
        (diff.coeff ((sw_choose n).1.val + ((sw_choose n).2 : ℚ) / (T : ℕ))) = _
    rw [h_n_eq, h_q_eq]
  -- sigma_of is injective.
  have h_sigma_inj : ∀ n₁ ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
      ∀ n₂ ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
      sigma_of n₁ = sigma_of n₂ → n₁ = n₂ := by
    intro n₁ _ n₂ _ h_eq
    have h_decomp_1 := h_sw_eq n₁
    have h_decomp_2 := h_sw_eq n₂
    have h_1 : (sw_choose n₁).1 = (sw_choose n₂).1 := by
      have : (sigma_of n₁).1 = (sigma_of n₂).1 := by rw [h_eq]
      exact this
    have h_2 : (sw_choose n₁).2 = (sw_choose n₂).2 := by
      have h_p1 : (sigma_of n₁).1 = (sigma_of n₂).1 := by rw [h_eq]
      have h_p2 : HEq (sigma_of n₁).2 (sigma_of n₂).2 := by rw [h_eq]
      have : HEq ((sw_choose n₁).2) ((sw_choose n₂).2) := h_p2
      exact eq_of_heq this
    apply Subtype.ext
    have h_q_eq : g + (n₁.val : ℚ) / (T : ℕ) = g + (n₂.val : ℚ) / (T : ℕ) := by
      rw [h_decomp_1, h_decomp_2, h_1, h_2]
    have : (n₁.val : ℚ) = (n₂.val : ℚ) := by
      have h_div : (n₁.val : ℚ) / (T : ℕ) = (n₂.val : ℚ) / (T : ℕ) := by linarith
      field_simp at h_div; exact h_div
    exact_mod_cast this
  -- sigma_of maps into FullSigma = Stilde_used.sigma w_range.
  have h_sigma_mem : ∀ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
      sigma_of n ∈ Stilde_used.sigma (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)) := by
    intro n _
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨n, Finset.mem_attach _ _, rfl⟩
    · rw [Finset.mem_range]
      have hs_used : (sw_choose n).1 ∈ Stilde_used :=
        Finset.mem_image.mpr ⟨n, Finset.mem_attach _ _, rfl⟩
      have h_n_M := h_n_le_M n.val n.property
      have h_decomp := h_sw_eq n
      have h_w_le : ((sw_choose n).2 : ℚ) / (T : ℕ) ≤ (M : ℚ) - (sw_choose n).1.val := by linarith
      have h_w_le' : ((sw_choose n).2 : ℚ) ≤ (T : ℚ) * ((M : ℚ) - (sw_choose n).1.val) := by
        have h_div_le := (div_le_iff₀ hT_pos).mp h_w_le
        linarith
      have h_w_int : ((sw_choose n).2 : ℤ) ≤ ⌊(T : ℚ) * ((M : ℚ) - (sw_choose n).1.val)⌋ :=
        Int.le_floor.mpr (by exact_mod_cast h_w_le')
      have h_floor_nonneg : 0 ≤ ⌊(T : ℚ) * ((M : ℚ) - (sw_choose n).1.val)⌋ := by
        have h_sval_le : ((sw_choose n).1.val : ℚ) ≤ M := h_used_sval_le _ hs_used
        apply Int.floor_nonneg.mpr
        apply mul_nonneg hT_pos.le; linarith
      have h_toNat_eq : ((W_s (sw_choose n).1 : ℕ) : ℤ) =
          ⌊(T : ℚ) * ((M : ℚ) - (sw_choose n).1.val)⌋ :=
        Int.toNat_of_nonneg h_floor_nonneg
      have h_final : (sw_choose n).2 ≤ W_s (sw_choose n).1 := by
        have h : ((sw_choose n).2 : ℤ) ≤ ((W_s (sw_choose n).1 : ℕ) : ℤ) := by
          rw [h_toNat_eq]; exact h_w_int
        exact_mod_cast h
      change (sw_choose n).2 < W_s (sw_choose n).1 + 1
      omega
  -- For p ∈ FullSigma \ Image(sigma_of), F(p) = 0.
  have h_zero_outside : ∀ q_sig ∈ Stilde_used.sigma
      (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
      q_sig ∉ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image sigma_of →
      F q_sig = 0 := by
    intro q_sig hq_sig h_not_im
    rcases q_sig with ⟨s, w⟩
    have hq_data := Finset.mem_sigma.mp hq_sig
    have hs_used : s ∈ Stilde_used := hq_data.1
    have hw_range : w ∈ Finset.range (W_s s + 1) := hq_data.2
    have hw_le_W : w ≤ W_s s := by
      have := Finset.mem_range.mp hw_range
      omega
    have h_sval_le_M_val : ((s.val : ℚ) + (w : ℚ) / (T : ℕ)) ≤ M := by
      have h_W_eq : ((W_s s : ℕ) : ℤ) = ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
        apply Int.toNat_of_nonneg
        apply Int.floor_nonneg.mpr
        apply mul_nonneg hT_pos.le
        have := h_used_sval_le _ hs_used; linarith
      have h_w_le_floor : (w : ℤ) ≤ ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
        rw [← h_W_eq]; exact_mod_cast hw_le_W
      have h_w_le_T : (w : ℚ) ≤ (T : ℚ) * ((M : ℚ) - s.val) := by
        have := Int.le_floor.mp h_w_le_floor
        exact_mod_cast this
      have h_div : (w : ℚ) / (T : ℕ) ≤ (M : ℚ) - s.val := by
        rw [div_le_iff₀ hT_pos]
        have h_w_le_T' : (w : ℚ) ≤ ((T : ℕ) : ℚ) * ((M : ℚ) - s.val) := h_w_le_T
        linarith
      linarith
    by_cases h_coeff : diff.coeff (s.val + (w : ℚ) / (T : ℕ)) = 0
    · change (pInvTQ p (T : ℕ)) ^ (n_s_int s + (w : ℤ)) *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
          (diff.coeff (s.val + (w : ℚ) / (T : ℕ))) = 0
      rw [h_coeff, map_zero, mul_zero]
    · exfalso
      have h_supp : (s.val + (w : ℚ) / (T : ℕ)) ∈ f.support := by
        by_contra h
        exact h_coeff (fhat_diff_coeff_outside_support hf2 h)
      let n_candidate : ℤ := n_s_int s + (w : ℤ)
      have h_q_n_cand : g + (n_candidate : ℚ) / (T : ℕ) = s.val + (w : ℚ) / (T : ℕ) := by
        have h_int := h_used_isInt _ hs_used
        have h_rewrite : (n_candidate : ℚ) = ((T : ℕ) : ℚ) * (s.val - g) + w := by
          change ((n_s_int s + (w : ℤ) : ℤ) : ℚ) = _
          push_cast
          linarith
        rw [h_rewrite]
        field_simp
        ring
      have h_n_cand_in_Tfp : n_candidate ∈
          Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M) := by
        apply (Set.Finite.mem_toFinset _).mpr
        refine ⟨?_, ?_⟩
        · rw [h_q_n_cand]; exact h_sval_le_M_val
        · rw [h_q_n_cand]; exact h_coeff
      have h_sigma_n_cand : sigma_of ⟨n_candidate, h_n_cand_in_Tfp⟩ =
          (⟨s, w⟩ : Σ _ : ↥(Stilde hf2), ℕ) := by
        change (⟨(sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩).1,
              (sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩).2⟩ : Σ _ : ↥(Stilde hf2), ℕ) =
            ⟨s, w⟩
        have h_eq := h_sw_unique ⟨n_candidate, h_n_cand_in_Tfp⟩ (s, w) h_q_n_cand
        -- h_eq : (s, w) = sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩
        rw [← h_eq]
      have h_in_im : (⟨s, w⟩ : Σ _ : ↥(Stilde hf2), ℕ) ∈
          (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image sigma_of := by
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨n_candidate, h_n_cand_in_Tfp⟩, Finset.mem_attach _ _, h_sigma_n_cand⟩
      exact h_not_im h_in_im
  -- Sum identity: via Finset.sum_image (injection) + Finset.sum_subset (extension).
  have h_sum_via_sigma :
      (∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
          (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
      ∑ p_sig ∈ Stilde_used.sigma (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
        F p_sig := by
    have h_eq : (∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
          (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
        ∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach, F (sigma_of n) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (h_F_eq n).symm
    rw [h_eq]
    rw [show (∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
              F (sigma_of n)) =
            ∑ p_sig ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image
              sigma_of, F p_sig from
          (Finset.sum_image h_sigma_inj).symm]
    apply Finset.sum_subset
    · intro p hp
      obtain ⟨n, hn_attach, hn_eq⟩ := Finset.mem_image.mp hp
      rw [← hn_eq]
      exact h_sigma_mem n hn_attach
    · intro p hp h_not_im
      exact h_zero_outside p hp h_not_im
  -- Convert FullSigma sum to nested via Finset.sum_sigma, then per_s_inner_sum_eq.
  have h_sigma_to_per_s :
      (∑ p_sig ∈ Stilde_used.sigma (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
        F p_sig) =
      ∑ s ∈ Stilde_used, (pInvTQ p (T : ℕ)) ^ (n_s_int s) *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
          (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro s _
    -- ∑ w ∈ range, F ⟨s, w⟩
    --   = ∑ w ∈ range, (pInvTQ)^{n_s + w} * algebraMap(diff.coeff(s.val + w/T))
    --   = (pInvTQ)^{n_s} * ∑ w ∈ range, (pInvTQ)^w * algebraMap(diff.coeff(s.val + w/T))
    --   = (pInvTQ)^{n_s} * algebraMap(Cs s - Cs_partial s (W_s + 1))  [per_s_inner_sum_eq]
    have hpInvTQ_ne_zero : pInvTQ p (T : ℕ) ≠ 0 := by
      intro h
      have hv := valued_v_pInvT (p := p) (T := T)
      rw [h] at hv
      simp at hv
    have h_pull_out : (∑ w ∈ Finset.range (W_s s + 1), F ⟨s, w⟩) =
        (pInvTQ p (T : ℕ)) ^ (n_s_int s) *
          ∑ w ∈ Finset.range (W_s s + 1), (pInvTQ p (T : ℕ)) ^ (w : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (s.val + (w : ℚ) / (T : ℕ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      change (pInvTQ p (T : ℕ)) ^ (n_s_int s + (w : ℤ)) *
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
            (diff.coeff (s.val + (w : ℚ) / (T : ℕ))) = _
      rw [zpow_add₀ hpInvTQ_ne_zero _ _]
      ring
    rw [h_pull_out]
    -- Apply per_s_inner_sum_eq.
    have h_inner := per_s_inner_sum_eq hf2 s (W_s s)
    rw [hdiff_def]
    rw [h_inner]
  -- Combine: LHS = nested ∑ s ∈ Stilde_used, (pInvTQ)^{n_s} * algebraMap(...).
  have h_LHS_eq :
      (∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M),
        (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
            (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
      ∑ s ∈ Stilde_used, (pInvTQ p (T : ℕ)) ^ (n_s_int s) *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
          (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) := by
    rw [← h_sigma_to_per_s, ← h_sum_via_sigma]
    rfl
  -- Now apply Valuation.map_sum_le using h_used_per_s_bound.
  rw [h_LHS_eq]
  apply Valuation.map_sum_le
  intro s hs
  exact h_used_per_s_bound s hs

/-- The bundled lift and the coefficientwise Teichmüller lift differ by a `T`-null
series. Grouping each partial sum by slice minima reduces the difference to tails of the
convergent coefficient bundles. -/
lemma fhat_diff_isTNullSeries
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)
      ∈ TNullSeriesIdeal p (T : ℕ) := by
  -- Structural prerequisites already in scope:
  -- * `Stilde_unique_decomposition` : unique `(s, w) : Stilde × ℕ` decomposition.
  -- * `not_Stilde_of_pos_w` : `w ≥ 1` ⇒ `q ∉ Stilde`.
  -- * `fhat_diff_coeff_Stilde` / `fhat_diff_coeff_outside_Stilde` /
  --   `fhat_diff_coeff_outside_support` : diff.coeff formulas at each location class.
  -- * `Cs_partial_diff_alg_v_le`: tail Cauchy bound.
  -- * `Cs_diff_alg_v_le`: limit bound
  --  `Valued.v (algebraMap (Cs s - Cs_partial s N)) ≤ ofAdd(-N)`.
  -- * `per_s_inner_sum_eq`: per-`s` inner-sum collapse to
  --   `algebraMap (Cs hf2 s - Cs_partial hf2 s (W + 1))`.
  intro g
  -- Set up notation.
  set diff : TLiftedPAdicHahnSeries p (T : ℕ) :=
    fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                (pAdicHahnSeries.coeff f) (support_IsPWO f)
    with hdiff_def
  -- The partial sum sequence.
  set P : ℕ → ℚᶜᵘⁿ_[p, (T : ℕ)] := fun M =>
    ∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M),
      (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (diff.coeff (g + (n.val : ℚ) / T))
    with hP_def
  -- We aim to show Tendsto P atTop (𝓝 0).  Use the Valued-topology characterisation:
  -- `(𝓝 0).HasBasis (fun γ : Γ₀ˣ => True) (fun γ => { x | Valued.v x < γ })`.
  -- KEY BOUND (analytical heart, structurally laid out below):
  --   `Valued.v (P M) ≤ ofAdd(-(⌊T·(M - g)⌋ + 1))`.
  -- As `M → ∞`, `⌊T·(M - g)⌋ → ∞`, so the bound `→ 0`, giving the result.
  --
  -- The bound follows from:
  -- (a) re-indexing `TfiniteBelow diff g M` over `(s, w) ∈ Stilde × ℕ` via
  --     `Stilde_unique_decomposition` (each `n ∈ TfiniteBelow` corresponds to a unique
  --     `(s, w)` with `g + n/T = s.val + w/T`);
  -- (b) for fixed `s`, per-`s` slice collapse via `per_s_inner_sum_eq`:
  --     `∑_w (pInvTQ)^w · algebraMap(diff.coeff(s.val + w/T))
  -- = algebraMap(Cs s - Cs_partial s (W_s + 1))`;
  -- (c) per-`s` valuation bound via `Cs_diff_alg_v_le`:
  --     `Valued.v((pInvTQ)^{n_s}
  -- · algebraMap(Cs s - Cs_partial s (W_s + 1))) ≤ ofAdd(-(n_s + W_s + 1))`;
  -- (d) arithmetic identity `n_s + W_s = ⌊T·(M - g)⌋` (residue condition implies);
  -- (e) ultrametric `Valuation.map_sum_le` over the (finite) Finset of active `s`s.

  -- Proof skeleton via the Valued neighbourhood characterisation:
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨c, hc_ne, hγ⟩ := Texists_v_lt_subset p (T : ℕ) hU
  -- It suffices to show: `∀ᶠ M, Valued.v (P M) < c`.
  suffices h_ev : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (P M) < c by
    filter_upwards [h_ev] with M hM
    exact hγ (by simpa using hM)
  -- Reduce to: `∀ᶠ M, Valued.v (P M) ≤ ofAdd(-(K + 1))` where K = ⌊T(M-g)⌋,
  -- and as M → ∞, K → ∞ makes the bound < c eventually.
  -- Step 1: extract the integer exponent `k` corresponding to `c`.
  set k : ℤ := Multiplicative.toAdd (WithZero.unzero hc_ne) with hk_def
  have h_γ_val : c =
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [hk_def, ofAdd_toAdd, WithZero.coe_unzero]
  -- Step 2: choose threshold M₀ so that for M ≥ M₀, ⌊T(M-g)⌋ ≥ -k.
  -- Concretely: pick M₀ := ⌈g + (-k)/T⌉₊.
  have hT_pos : (0 : ℚ) < (T : ℕ) := by exact_mod_cast T.pos
  have hT_ne : ((T : ℕ) : ℚ) ≠ 0 := ne_of_gt hT_pos
  have h_ev_floor : ∀ᶠ M : ℕ in Filter.atTop,
      -k ≤ ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
    have h_int : ∀ᶠ M : ℕ in Filter.atTop, ⌈g + (-(k : ℚ)) / T⌉₊ ≤ M :=
      Filter.eventually_ge_atTop ⌈g + (-(k : ℚ)) / T⌉₊
    filter_upwards [h_int] with M hM
    have h1 : g + (-(k : ℚ)) / T ≤ (⌈g + (-(k : ℚ)) / T⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((⌈g + (-(k : ℚ)) / T⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    have h3 : g + (-(k : ℚ)) / T ≤ (M : ℚ) := h1.trans h2
    have h4 : (-(k : ℚ)) / T ≤ (M : ℚ) - g := by linarith
    have h5 : (T : ℚ) * ((-(k : ℚ)) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
      mul_le_mul_of_nonneg_left h4 hT_pos.le
    have hT_eq : (T : ℚ) * ((-(k : ℚ)) / T) = -(k : ℚ) := by
      rw [mul_div_assoc']; field_simp
    rw [hT_eq] at h5
    have h6 : (-(k : ℤ) : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := by linarith
    exact Int.le_floor.mpr h6
  filter_upwards [h_ev_floor] with M hMfloor
  -- Step 3: apply fhat_diff_partial_v_le to get the per-M bound.
  have h_partial_le := fhat_diff_partial_v_le hf2 g M
  -- Unfold the partial-sum expression so it matches P M / hP_def.
  have h_P_eq : P M =
      ∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ)
                  (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)) g M),
              (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
                algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
                  ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
                    (g + (n.val : ℚ) / T)) := by
    rw [hP_def]
  rw [h_P_eq]
  -- Step 4: chain the per-M bound and the threshold into < γ.
  refine lt_of_le_of_lt h_partial_le ?_
  rw [h_γ_val]
  rw [WithZero.coe_lt_coe]
  apply Multiplicative.ofAdd_lt.mpr
  linarith

end CoefficientCosets

end PAdicOrderType
