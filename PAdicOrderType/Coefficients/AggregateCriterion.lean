/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateData

/-!
# Coefficient expansions and multiplicity weights

For digit vectors representing `-T·Supp(f)` modulo `ℤ`, this file supplies the
coefficient expansion of `P(f̂)`, the slice functions `muQFun` and `aggExpFun`,
and their multiplicity weights `muWeight` and `aggWeight`. It also decomposes
support elements of powers into multisets of support elements.

These identities relate multiplicity weights to the carry-free coefficient formula
and the polynomial estimate used in finite-rank exclusion. They supply the expansion of
`P(g̃)` and of the coefficients of the powers `g̃ ^ k` in the proof of Proposition 3.4.
-/

namespace PAdicOrderType

open RamifiedCoefficients CoefficientCosets Multiplicity TrustworthyKedlaya

variable {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+} {D : Set DigitSeries}

/-! ### The `T`-null expansion identity -/

/-- Per-coefficient expansion of `P(f̂)`: for `P.natDegree ≤ n` and every `q ∈ ℚ`,
`(P(f̂))_q = ∑_{i ≤ n} OQpCUn_embd (P.coeff i) · (f̂^i)_q`. -/
lemma aeval_fhat_coeff_eq
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (P : Polynomial ℤᶜᵘⁿ_[p]) {n : ℕ} (hdeg : P.natDegree ≤ n) (q : ℚ) :
    ((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff q =
      ∑ i ∈ Finset.range (n + 1),
        OQpCUn_embd p T (P.coeff i) * ((fhat hf2) ^ i).coeff q := by
  have hlt : (P.map (OQpCUn_embd p T)).natDegree < n + 1 :=
    lt_of_le_of_lt (le_trans Polynomial.natDegree_map_le hdeg) (Nat.lt_succ_self n)
  rw [Polynomial.aeval_eq_sum_range' hlt, HahnSeries.coeff_sum]
  congr 1
  ext i
  rw [Polynomial.coeff_map, Algebra.smul_def]
  change ((HahnSeries.single 0 _) * (fhat hf2) ^ i).coeff q = _
  rw [HahnSeries.single_zero_mul_eq_smul]
  rfl

/-!
### Pointwise slice data on digit vectors

Proof-free versions of `muQ` and `aggExp`, extended by `0` off `D`, so
that sums over supports of multiplicity functions need no membership proofs.
-/

open Classical in
/-- The slice minimum `s_d = muQ hf2 d`, extended by `0` off `D`. -/
noncomputable def muQFun
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    DigitSeries → ℚ :=
  fun d => if hd : d ∈ D then muQ hf2 ⟨d, hd⟩ else 0

lemma muQFun_apply_of_mem
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d : DigitSeries} (hd : d ∈ D) :
    muQFun hf2 d = muQ hf2 ⟨d, hd⟩ := by
  unfold muQFun
  exact dif_pos hd

lemma muQFun_mem_stilde
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d : DigitSeries} (hd : d ∈ D) :
    muQFun hf2 d ∈ Stilde hf2 := by
  rw [muQFun_apply_of_mem hf2 hd]
  exact ⟨⟨d, hd⟩, rfl⟩

lemma muQFun_injOn (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Set.InjOn (muQFun hf2) D := by
  intro d hd e he h
  rw [muQFun_apply_of_mem hf2 hd, muQFun_apply_of_mem hf2 he] at h
  exact congrArg Subtype.val (muQ_injective hD hf2 h)

open Classical in
/-- The integer exponent `l₀(d) = ‖d‖ + T·s_d`, extended by `0` off `D`. -/
noncomputable def aggExpFun
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    DigitSeries → ℤ :=
  fun d => if hd : d ∈ D then aggExp hf2 ⟨d, hd⟩ else 0

lemma aggExpFun_apply_of_mem
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d : DigitSeries} (hd : d ∈ D) :
    aggExpFun hf2 d = aggExp hf2 ⟨d, hd⟩ := by
  unfold aggExpFun
  exact dif_pos hd

lemma aggExpFun_cast
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d : DigitSeries} (hd : d ∈ D) :
    ((aggExpFun hf2 d : ℤ) : ℚ) = (d.norm p : ℚ) + (T : ℚ) * muQFun hf2 d := by
  rw [aggExpFun_apply_of_mem hf2 hd, muQFun_apply_of_mem hf2 hd]
  exact aggExp_cast hf2 ⟨d, hd⟩

/-! ### Weights of multiplicity functions -/

/-- The `muQ`-weight `∑_d φ(d)·s_d ∈ ℚ` of a multiplicity function: the
exponent at which `φ` contributes to a power of `f̂`. -/
noncomputable def muWeight
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (φ : DigitSeries →₀ ℕ) : ℚ :=
  ∑ d ∈ φ.support, (φ d : ℚ) * muQFun hf2 d

/-- The integer weight `w(φ) = ∑_d φ(d)·l₀(d) ∈ ℤ` of a multiplicity function:
the `pInvTQ`-exponent of the corresponding aggregate term. -/
noncomputable def aggWeight
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (φ : DigitSeries →₀ ℕ) : ℤ :=
  ∑ d ∈ φ.support, (φ d : ℤ) * aggExpFun hf2 d

/-- `w(φ) = T·(muQ-weight of φ) + ‖Σ(φ)‖`: the two weights measure the same
exponent, in the normalizations of `pInvTQ` and of `t`, respectively. -/
lemma aggWeight_cast
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {φ : DigitSeries →₀ ℕ} (hsub : ↑φ.support ⊆ D) :
    ((aggWeight hf2 φ : ℤ) : ℚ) =
      (T : ℚ) * muWeight hf2 φ + ((total φ).norm p : ℚ) := by
  unfold aggWeight muWeight
  rw [norm_total p φ]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aggExpFun_cast hf2 (hsub hd)]
  ring

/-- The residue property of the `muQ`-weight: `T·(muQ-weight) + ‖Σ(φ)‖ ∈ ℤ`
(the finsupp form of `muQ_residue`). -/
lemma isInt_mul_muWeight_add_norm
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {φ : DigitSeries →₀ ℕ} (hsub : ↑φ.support ⊆ D) :
    ((T : ℚ) * muWeight hf2 φ + ((total φ).norm p : ℚ)).isInt = true := by
  rw [← aggWeight_cast hf2 hsub]
  exact isInt_intCast' _

/-! ### The pullback of `Stilde` along `muQ` -/

open Classical in
/-- A choice of `muQ`-preimage in `D` for each element of `Stilde`, extended by
`0` elsewhere. -/
noncomputable def stildePullback (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    ℚ → DigitSeries :=
  fun a => if h : a ∈ Stilde hf2 then ((muEquiv hD hf2).symm ⟨a, h⟩ : ↥D).val else 0

lemma stildePullback_mem (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {a : ℚ} (h : a ∈ Stilde hf2) :
    stildePullback hD hf2 a ∈ D := by
  unfold stildePullback
  rw [dif_pos h]
  exact ((muEquiv hD hf2).symm ⟨a, h⟩).property

lemma muQFun_stildePullback (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {a : ℚ} (h : a ∈ Stilde hf2) :
    muQFun hf2 (stildePullback hD hf2 a) = a := by
  have hmem : stildePullback hD hf2 a ∈ D := stildePullback_mem hD hf2 h
  rw [muQFun_apply_of_mem hf2 hmem]
  have hval : stildePullback hD hf2 a = ((muEquiv hD hf2).symm ⟨a, h⟩ : ↥D).val := by
    unfold stildePullback
    exact dif_pos h
  have h1 : (⟨stildePullback hD hf2 a, hmem⟩ : ↥D) = (muEquiv hD hf2).symm ⟨a, h⟩ :=
    Subtype.ext hval
  rw [h1]
  have h2 : muToStilde hf2 ((muEquiv hD hf2).symm ⟨a, h⟩) = ⟨a, h⟩ :=
    (muEquiv hD hf2).apply_symm_apply ⟨a, h⟩
  exact congrArg Subtype.val h2

/-! ### Multiset decomposition of powers -/

/-- Multiset decomposition of the support of a Hahn-series power: if
`q ∈ (x ^ i).support` and the coefficient support of `x` is contained in `V`,
then `q` is a sum of `i` elements of `V` (with multiplicity), as for the tuples
`(q₁, …, q_k)` in the proof of Proposition 3.4. -/
lemma exists_multiset_of_mem_support_pow {x : TLiftedPAdicHahnSeries p (T : ℕ)}
    {V : Set ℚ} (h_supp : Function.support x.coeff ⊆ V) :
    ∀ (i : ℕ) {q : ℚ}, q ∈ (x ^ i).support →
      ∃ l : Multiset ℚ, Multiset.card l = i ∧ (∀ a ∈ l, a ∈ V) ∧ l.sum = q := by
  intro i
  induction i with
  | zero =>
    intro q hq
    have hq0 : q = 0 := by
      simpa [pow_zero, HahnSeries.support_one] using hq
    exact ⟨0, by simp, by simp, by simp [hq0]⟩
  | succ i ih =>
    intro q hq
    have hq' : q ∈ (x ^ i * x).support := by
      simpa [pow_succ] using hq
    have h_sub := HahnSeries.support_mul_subset hq'
    rcases (by simpa [Set.mem_add] using h_sub) with ⟨a, ha_supp, b, hb_supp, hab⟩
    have hb_ne : x.coeff b ≠ 0 := by
      simpa [HahnSeries.mem_support] using hb_supp
    have hb_fun : b ∈ Function.support x.coeff := by
      simpa [Function.mem_support] using hb_ne
    obtain ⟨l, hl_card, hl_mem, hl_sum⟩ := ih ha_supp
    refine ⟨b ::ₘ l, by simp [hl_card], ?_, ?_⟩
    · intro a' ha'
      rcases Multiset.mem_cons.mp ha' with h1 | h2
      · rw [h1]
        exact h_supp hb_fun
      · exact hl_mem a' h2
    · rw [Multiset.sum_cons, hl_sum, add_comm]
      exact hab

end PAdicOrderType
