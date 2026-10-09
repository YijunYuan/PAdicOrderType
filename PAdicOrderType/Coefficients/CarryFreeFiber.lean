/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateCriterion
import PAdicOrderType.Digits.BlockInterleavings

/-!
# The carry-free fiber and the multinomial formula at a residue-matching exponent

This file formalizes the coefficient computation behind identity (3.6) in the proof of
Proposition 3.4. Multiplicity functions contributing to a residue-matching coefficient satisfy
an abstract *collapse hypothesis*, the rigid condition of Definition 3.3

`hcol : ∀ φ, ↑φ.support ⊆ D → card φ ≤ n → (‖Σ(φ)‖ - ‖u‖).isInt → card φ = n ∧ Σ(φ) = u`

(in the application, `MarkerData.carry_free`). Under this hypothesis:

- `PAdicOrderType.fhat_pow_coeff_eq_zero_of_lt_cf`: at an exponent `q` with
  `T q + ‖u‖ ∈ ℤ`, the coefficients of `f̂ ^ i` vanish for `i < n`;
- `PAdicOrderType.fhat_pow_coeff_eq_sum_carryFreeFiber`: the coefficient of
  `f̂ ^ n` at such `q` is the sum over the *carry-free fiber*
  `carryFreeFiber n D u = {φ | supp φ ⊆ D, |φ| = n, Σ(φ) = u}` of `muQ`-weight `q`
  of the multinomial coefficient times the product of coefficient bundles;
- `PAdicOrderType.totalSum_eq_carryFree`: for any finite set `W` of integers
  containing all `w` at which `P(f̂)` has a nonzero coefficient on the coset
  `-‖u‖/T + w/T`, the total `∑_{w ∈ W} p^{w/T} (P(f̂))_{-‖u‖/T + w/T}` equals
  `a_n · [X^u] (H_D)^n`, where `H_D = ∑_{d ∈ D} A_d X^d` (`coefficientFamily p D (adFun hf2)`)
  and `a_n` is the top coefficient of `P` (`natDegree P = n`). For monic `P`, the right-hand
  side is the sum `S_n(u)` of identity (3.6).
-/

namespace PAdicOrderType

open RamifiedCoefficients CoefficientCosets Multiplicity

variable {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+} {D : Set DigitSeries}

/-- The **carry-free fiber**: multiplicity functions supported in `D` of total
multiplicity `n` and exact digit-vector sum `u`. Up to reordering, these index the nonzero
terms of the sum `S_n(u)` of (3.4). -/
def carryFreeFiber (n : ℕ) (D : Set DigitSeries) (u : DigitSeries) :
    Set (DigitSeries →₀ ℕ) :=
  {φ | ↑φ.support ⊆ D ∧ card φ = n ∧ total φ = u}

lemma carryFreeFiber_subset_powFiber (n : ℕ) (D : Set DigitSeries) (u : DigitSeries) :
    carryFreeFiber n D u ⊆ powFiber n u := fun _ hφ => ⟨hφ.2.1, hφ.2.2⟩

/-- The carry-free fiber is finite, as a subset of the finite multiplicity fiber with fixed
total multiplicity and digit-vector sum. -/
theorem carryFreeFiber_finite (n : ℕ) (D : Set DigitSeries) (u : DigitSeries) :
    (carryFreeFiber n D u).Finite :=
  (powFiber_finite n u).subset (carryFreeFiber_subset_powFiber n D u)

/-- The **collapse hypothesis** abstracting `MarkerData.carry_free`: every
multiplicity function on `D` of total multiplicity `≤ n` whose digit-vector sum
represents `‖u‖` modulo `ℤ` has total multiplicity exactly `n` and digit-vector
sum exactly `u`. This is the `(g, R, T, n)`-rigid condition of Definition 3.3, stated for
multisets of digit vectors instead of tuples. -/
def IsCollapse (n : ℕ) (D : Set DigitSeries) (u : DigitSeries) : Prop :=
  ∀ φ : DigitSeries →₀ ℕ, ↑φ.support ⊆ D → card φ ≤ n →
    (((total φ).norm p : ℚ) - (u.norm p : ℚ)).isInt = true → card φ = n ∧ total φ = u

/-! ### The support of the carry-free fiber -/

/-- The (finite) union of the supports of the members of the carry-free fiber
`carryFreeFiber n D u`. -/
noncomputable def carryFreeFiberSupport (n : ℕ) (D : Set DigitSeries) (u : DigitSeries) :
    Finset DigitSeries :=
  (Set.Finite.biUnion (carryFreeFiber_finite n D u)
    fun φ _ => φ.support.finite_toSet).toFinset

lemma mem_carryFreeFiberSupport {n : ℕ} {D : Set DigitSeries} {u d : DigitSeries} :
    d ∈ carryFreeFiberSupport n D u ↔ ∃ φ ∈ carryFreeFiber n D u, d ∈ φ.support := by
  unfold carryFreeFiberSupport
  rw [Set.Finite.mem_toFinset]
  simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]

lemma carryFreeFiberSupport_subset {n : ℕ} {D : Set DigitSeries} {u : DigitSeries} :
    ↑(carryFreeFiberSupport n D u) ⊆ D := by
  intro d hd
  obtain ⟨φ, hφ, hdφ⟩ := mem_carryFreeFiberSupport.mp hd
  exact hφ.1 hdφ

lemma support_subset_carryFreeFiberSupport {n : ℕ} {D : Set DigitSeries} {u : DigitSeries}
    {φ : DigitSeries →₀ ℕ} (hφ : φ ∈ carryFreeFiber n D u) :
    φ.support ⊆ carryFreeFiberSupport n D u :=
  fun _ hd => mem_carryFreeFiberSupport.mpr ⟨φ, hφ, hd⟩

/-! ### The abstract collapse -/

/-- **The collapse, finsupp form**: if a multiplicity function `φ` on `D` has
`|φ| ≤ n` and its `muQ`-weight `q` matches the residue `-‖u‖/T` modulo
`(1/T)ℤ`, then under the collapse hypothesis `φ` lies in the carry-free fiber
(and in particular `|φ| = n`). -/
lemma mem_carryFreeFiber_of_muWeight
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {n : ℕ} {u : DigitSeries} (hcol : IsCollapse (p := p) n D u)
    {φ : DigitSeries →₀ ℕ} (hsub : ↑φ.support ⊆ D) (hcard : card φ ≤ n)
    {q : ℚ} (hw : muWeight hf2 φ = q)
    (hres : ((T : ℚ) * q + (u.norm p : ℚ)).isInt = true) :
    card φ = n ∧ φ ∈ carryFreeFiber n D u := by
  have h1 := isInt_mul_muWeight_add_norm hf2 hsub
  rw [hw] at h1
  have hnorm : (((total φ).norm p : ℚ) - (u.norm p : ℚ)).isInt = true := by
    have h2 : ((total φ).norm p : ℚ) - (u.norm p : ℚ) =
        ((T : ℚ) * q + ((total φ).norm p : ℚ)) -
          ((T : ℚ) * q + (u.norm p : ℚ)) := by ring
    rw [h2]
    exact isInt_sub' h1 hres
  obtain ⟨hcn, htu⟩ := hcol φ hsub hcard hnorm
  exact ⟨hcn, ⟨hsub, hcn, htu⟩⟩

/-- **The collapse, multiset form**: a multiset of `i ≤ n` elements of
`Stilde` summing to a residue-matching exponent `q` forces `i = n`, and its
pullback along `muQ` is a member of the carry-free fiber; in particular every
element of the multiset is the slice minimum `s_d` of a digit vector `d`
appearing in the support of a fiber member. -/
lemma collapse_of_multiset_cf (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {n : ℕ} {u : DigitSeries} (hcol : IsCollapse (p := p) n D u)
    {i : ℕ} (hi : i ≤ n) {l : Multiset ℚ} (hlS : ∀ a ∈ l, a ∈ Stilde hf2)
    (hlcard : Multiset.card l = i) {q : ℚ} (hlsum : l.sum = q)
    (hres : ((T : ℚ) * q + (u.norm p : ℚ)).isInt = true) :
    i = n ∧ ∃ φ ∈ carryFreeFiber n D u,
      muWeight hf2 φ = q ∧ ∀ a ∈ l, ∃ d ∈ φ.support, muQFun hf2 d = a := by
  classical
  set l' : Multiset DigitSeries := l.map (stildePullback hD hf2) with hl'
  set φ : DigitSeries →₀ ℕ := l'.toFinsupp with hφdef
  have hsupp : φ.support = l'.toFinset := Multiset.toFinsupp_support l'
  have hmem_l' : ∀ d ∈ l', d ∈ D := by
    intro d hd
    rcases Multiset.mem_map.mp hd with ⟨a, ha, rfl⟩
    exact stildePullback_mem hD hf2 (hlS a ha)
  have hsubD : ↑φ.support ⊆ D := by
    intro d hd
    rw [hsupp] at hd
    exact hmem_l' d (Multiset.mem_toFinset.mp hd)
  -- `l` is recovered from `l'` by `muQFun`.
  have hl_back : l'.map (muQFun hf2) = l := by
    rw [hl', Multiset.map_map]
    have h1 : l.map (muQFun hf2 ∘ stildePullback hD hf2) = l.map id :=
      Multiset.map_congr rfl fun a ha => muQFun_stildePullback hD hf2 (hlS a ha)
    rw [h1, Multiset.map_id]
  -- `|φ| = i`.
  have hφcard : card φ = i := by
    rw [card_eq_sum]
    have h1 : ∀ d ∈ φ.support, φ d = l'.count d := fun d _ => Multiset.toFinsupp_apply l' d
    rw [Finset.sum_congr rfl h1, hsupp, Multiset.toFinset_sum_count_eq, hl',
      Multiset.card_map, hlcard]
  -- `muWeight φ = q`.
  have hφweight : muWeight hf2 φ = q := by
    unfold muWeight
    have h1 : ∀ d ∈ φ.support, (φ d : ℚ) * muQFun hf2 d = l'.count d • muQFun hf2 d := by
      intro d _
      rw [Multiset.toFinsupp_apply l' d, nsmul_eq_mul]
    rw [Finset.sum_congr rfl h1, hsupp, ← Finset.sum_multiset_map_count, hl_back, hlsum]
  -- collapse
  obtain ⟨hcn, hφfib⟩ := mem_carryFreeFiber_of_muWeight hf2 hcol hsubD
    (hφcard.le.trans hi) hφweight hres
  refine ⟨hφcard.symm.trans hcn, φ, hφfib, hφweight, ?_⟩
  intro a ha
  refine ⟨stildePullback hD hf2 a, ?_, muQFun_stildePullback hD hf2 (hlS a ha)⟩
  rw [hsupp, Multiset.mem_toFinset, hl']
  exact Multiset.mem_map_of_mem _ ha

/-! ### Private arithmetic helpers for the carry-free coefficient formula -/

private lemma zpow_finset_sum_cf {G₀ : Type*} [CommGroupWithZero G₀] {x : G₀} (hx : x ≠ 0)
    {α : Type*} (s : Finset α) (g : α → ℤ) :
    x ^ (∑ a ∈ s, g a) = ∏ a ∈ s, x ^ g a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

private lemma natCast_hahn_cf (m : ℕ) :
    ((m : ℕ) : TLiftedPAdicHahnSeries p (T : ℕ)) =
      HahnSeries.single (0 : ℚ) ((m : ℕ) : ℤᶜᵘⁿ_[p,(T : ℕ)]) := by
  rw [← map_natCast (HahnSeries.C :
    ℤᶜᵘⁿ_[p,(T : ℕ)] →+* TLiftedPAdicHahnSeries p (T : ℕ)) m]
  rfl

private lemma sum_apply_superset_cf {φ : DigitSeries →₀ ℕ} {s : Finset DigitSeries}
    (h : φ.support ⊆ s) : ∑ d ∈ s, φ d = card φ := by
  rw [card_eq_sum]
  exact (Finset.sum_subset h fun d _ hd => Finsupp.notMem_support_iff.mp hd).symm

private lemma muWeight_eq_sum_superset_cf
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {φ : DigitSeries →₀ ℕ} {s : Finset DigitSeries} (h : φ.support ⊆ s) :
    ∑ d ∈ s, φ d • muQFun hf2 d = muWeight hf2 φ := by
  unfold muWeight
  rw [← Finset.sum_subset h fun d _ hd => by
    rw [Finsupp.notMem_support_iff.mp hd, zero_smul]]
  exact Finset.sum_congr rfl fun d _ => nsmul_eq_mul _ _

/-- Vanishing below the top degree under the collapse hypothesis: as in the proof of
Proposition 3.4, the lower powers do not contribute on the residue class of `u`. -/
theorem fhat_pow_coeff_eq_zero_of_lt_cf (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {n : ℕ} {u : DigitSeries} (hcol : IsCollapse (p := p) n D u)
    {i : ℕ} (hi : i < n) {q : ℚ}
    (hres : ((T : ℚ) * q + (u.norm p : ℚ)).isInt = true) :
    ((fhat hf2) ^ i).coeff q = 0 := by
  by_contra hne
  have hq_mem : q ∈ ((fhat hf2) ^ i).support := by
    simpa [HahnSeries.mem_support] using hne
  obtain ⟨l, hlc, hlm, hls⟩ :=
    exists_multiset_of_mem_support_pow (fhat_support_subset hf2) i hq_mem
  obtain ⟨heq, -⟩ :=
    collapse_of_multiset_cf hD hf2 hcol hi.le hlm hlc hls hres
  omega

/-- The multinomial formula at a residue-matching exponent under the collapse
hypothesis, used in the proof of Proposition 3.4. -/
theorem fhat_pow_coeff_eq_sum_carryFreeFiber (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {n : ℕ} {u : DigitSeries} (hcol : IsCollapse (p := p) n D u) {q : ℚ}
    (hres : ((T : ℚ) * q + (u.norm p : ℚ)).isInt = true) :
    ((fhat hf2) ^ n).coeff q =
      ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
        if muWeight hf2 φ = q then
          (Nat.multinomial φ.support φ : ℤᶜᵘⁿ_[p,(T : ℕ)]) *
            ∏ d ∈ φ.support, (fhat hf2).coeff (muQFun hf2 d) ^ φ d
        else 0 := by
  classical
  set D₀ : Finset DigitSeries := carryFreeFiberSupport n D u with hD₀
  have hD₀D : ↑D₀ ⊆ D := fun d hd => carryFreeFiberSupport_subset hd
  have hinj : Set.InjOn (muQFun hf2) ↑D₀ := (muQFun_injOn hD hf2).mono hD₀D
  set A₀ : Finset ℚ := D₀.image (muQFun hf2) with hA₀
  have himage_Stilde : ↑A₀ ⊆ Stilde hf2 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨d, hd, rfl⟩
    exact muQFun_mem_stilde hf2 (hD₀D hd)
  -- the truncation of `fhat` to the exponents of `D₀`
  set trunc : TLiftedPAdicHahnSeries p (T : ℕ) :=
    ∑ d ∈ D₀, HahnSeries.single (muQFun hf2 d) ((fhat hf2).coeff (muQFun hf2 d))
    with htrunc
  set rest : TLiftedPAdicHahnSeries p (T : ℕ) := fhat hf2 - trunc with hrest
  -- coefficients of `trunc`
  have htrunc_coeff_mem : ∀ a ∈ A₀, trunc.coeff a = (fhat hf2).coeff a := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨d, hd, rfl⟩
    rw [htrunc, HahnSeries.coeff_sum, Finset.sum_eq_single d]
    · rw [HahnSeries.coeff_single_same]
    · intro e he hne
      rw [HahnSeries.coeff_single, if_neg]
      intro heq
      exact hne (hinj he hd heq.symm)
    · intro hdne
      exact absurd hd hdne
  have htrunc_coeff_notmem : ∀ a, a ∉ A₀ → trunc.coeff a = 0 := by
    intro a ha
    rw [htrunc, HahnSeries.coeff_sum]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [HahnSeries.coeff_single, if_neg]
    intro heq
    refine ha ?_
    rw [heq]
    exact Finset.mem_image_of_mem _ hd
  have htrunc_supp : Function.support trunc.coeff ⊆ ↑A₀ := by
    intro a ha
    by_contra hnot
    exact ha (htrunc_coeff_notmem a fun h => hnot h)
  have hrest_supp : Function.support rest.coeff ⊆ Stilde hf2 \ ↑A₀ := by
    intro a ha
    have ha' : rest.coeff a ≠ 0 := ha
    have hcoeff_eq : rest.coeff a = (fhat hf2).coeff a - trunc.coeff a := by
      rw [hrest, HahnSeries.coeff_sub]
    constructor
    · by_contra hnot
      apply ha'
      have h1 : (fhat hf2).coeff a = 0 := by
        by_contra h
        exact hnot (fhat_support_subset hf2 h)
      have h2 : trunc.coeff a = 0 :=
        htrunc_coeff_notmem a fun hmem => hnot (himage_Stilde hmem)
      rw [hcoeff_eq, h1, h2, sub_zero]
    · intro hmem
      apply ha'
      rw [hcoeff_eq, htrunc_coeff_mem a hmem, sub_self]
  have hsplit : fhat hf2 = trunc + rest := by
    rw [hrest]
    ring
  -- cross terms vanish by the collapse
  have hcross : ∀ k, k < n → (trunc ^ k * rest ^ (n - k)).coeff q = 0 := by
    intro k hk
    by_contra hne
    have hq_mem : q ∈ (trunc ^ k * rest ^ (n - k)).support := by
      simpa [HahnSeries.mem_support] using hne
    have h_sub := HahnSeries.support_mul_subset hq_mem
    rcases (by simpa [Set.mem_add] using h_sub) with ⟨q₁, hq₁, q₂, hq₂, hq12⟩
    obtain ⟨l₁, hl₁c, hl₁m, hl₁s⟩ := exists_multiset_of_mem_support_pow htrunc_supp k hq₁
    obtain ⟨l₂, hl₂c, hl₂m, hl₂s⟩ := exists_multiset_of_mem_support_pow hrest_supp (n - k) hq₂
    have hlc : Multiset.card (l₁ + l₂) = n := by
      rw [Multiset.card_add, hl₁c, hl₂c]
      omega
    have hlS : ∀ a ∈ l₁ + l₂, a ∈ Stilde hf2 := by
      intro a ha
      rcases Multiset.mem_add.mp ha with h1 | h2
      · exact himage_Stilde (hl₁m a h1)
      · exact (hl₂m a h2).1
    have hls : (l₁ + l₂).sum = q := by
      rw [Multiset.sum_add, hl₁s, hl₂s, hq12]
    obtain ⟨-, φ, hφfib, -, hall⟩ :=
      collapse_of_multiset_cf hD hf2 hcol le_rfl hlS hlc hls hres
    have hl₂ne : l₂ ≠ 0 := by
      intro h0
      rw [h0, Multiset.card_zero] at hl₂c
      omega
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hl₂ne
    obtain ⟨d, hdφ, hdb⟩ := hall b (Multiset.mem_add.mpr (Or.inr hb))
    refine (hl₂m b hb).2 ?_
    have hdD₀ : d ∈ D₀ := support_subset_carryFreeFiberSupport hφfib hdφ
    rw [← hdb]
    exact Finset.mem_image_of_mem _ hdD₀
  -- the coefficient reduces to the truncation
  have hpow_red : ((fhat hf2) ^ n).coeff q = (trunc ^ n).coeff q := by
    rw [hsplit, add_pow, HahnSeries.coeff_sum, Finset.sum_range_succ]
    have hlast : (trunc ^ n * rest ^ (n - n) *
        ((n.choose n : ℕ) : TLiftedPAdicHahnSeries p (T : ℕ))).coeff q =
        (trunc ^ n).coeff q := by
      rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
    rw [hlast, Finset.sum_eq_zero, zero_add]
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [mul_comm (trunc ^ k * rest ^ (n - k)) _, natCast_hahn_cf,
      HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, hcross k hk',
      smul_zero]
  -- products of singles collapse to a single
  have prod_single : ∀ (s : Finset DigitSeries) (av : DigitSeries → ℚ)
      (rv : DigitSeries → ℤᶜᵘⁿ_[p,(T : ℕ)]),
      ∏ d ∈ s, HahnSeries.single (av d) (rv d) =
        HahnSeries.single (∑ d ∈ s, av d) (∏ d ∈ s, rv d) := by
    intro s av rv
    induction s using Finset.induction with
    | empty => simp
    | insert d s hd ih =>
      rw [Finset.prod_insert hd, ih, Finset.sum_insert hd, Finset.prod_insert hd]
      exact HahnSeries.single_mul_single
  -- multinomial expansion of the truncated power
  have htrunc_pow : (trunc ^ n).coeff q =
      ∑ k ∈ D₀.piAntidiag n,
        if (∑ d ∈ D₀, k d • muQFun hf2 d) = q then
          (Nat.multinomial D₀ k : ℤᶜᵘⁿ_[p,(T : ℕ)]) *
            ∏ d ∈ D₀, (fhat hf2).coeff (muQFun hf2 d) ^ k d
        else 0 := by
    rw [htrunc, Finset.sum_pow_eq_sum_piAntidiag, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_congr rfl fun d _ =>
        HahnSeries.single_pow (muQFun hf2 d) (k d) ((fhat hf2).coeff (muQFun hf2 d)),
      prod_single, natCast_hahn_cf, HahnSeries.single_mul_single, zero_add,
      HahnSeries.coeff_single]
    by_cases hcond : (∑ d ∈ D₀, k d • muQFun hf2 d) = q
    · rw [if_pos hcond.symm, if_pos hcond]
    · rw [if_neg (fun h => hcond h.symm), if_neg hcond]
  -- reindex the surviving multiplicity vectors by the carry-free fiber
  set toFs : (DigitSeries → ℕ) → (DigitSeries →₀ ℕ) := fun k =>
    Finsupp.onFinset D₀ (fun d => if d ∈ D₀ then k d else 0)
      (fun d hd => by
        by_cases h : d ∈ D₀
        · exact h
        · simp [h] at hd) with htoFs
  have htoFs_apply : ∀ (k : DigitSeries → ℕ), (∀ d, k d ≠ 0 → d ∈ D₀) →
      ∀ d, toFs k d = k d := by
    intro k hk d
    rw [htoFs]
    simp only [Finsupp.onFinset_apply]
    by_cases h : d ∈ D₀
    · rw [if_pos h]
    · rw [if_neg h]
      exact (not_ne_iff.mp fun hne => h (hk d hne)).symm
  have hreindex :
      (∑ k ∈ D₀.piAntidiag n,
        if (∑ d ∈ D₀, k d • muQFun hf2 d) = q then
          (Nat.multinomial D₀ k : ℤᶜᵘⁿ_[p,(T : ℕ)]) *
            ∏ d ∈ D₀, (fhat hf2).coeff (muQFun hf2 d) ^ k d
        else 0) =
      ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
        if muWeight hf2 φ = q then
          (Nat.multinomial φ.support φ : ℤᶜᵘⁿ_[p,(T : ℕ)]) *
            ∏ d ∈ φ.support, (fhat hf2).coeff (muQFun hf2 d) ^ φ d
        else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (i := toFs) (j := fun φ => ⇑φ) ?_ ?_ ?_ ?_ ?_
    · -- `toFs` lands in the fiber filter
      intro k hk
      rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
      obtain ⟨⟨hsum, hksupp⟩, hw⟩ := hk
      have happ := htoFs_apply k hksupp
      have hsupp_sub : (toFs k).support ⊆ D₀ := Finsupp.support_onFinset_subset
      have hcard : card (toFs k) = n := by
        rw [← sum_apply_superset_cf hsupp_sub, Finset.sum_congr rfl fun d _ => happ d]
        exact hsum
      have hweight : muWeight hf2 (toFs k) = q := by
        rw [← muWeight_eq_sum_superset_cf hf2 hsupp_sub,
          Finset.sum_congr rfl fun d _ => by rw [happ d]]
        exact hw
      have hsubD' : ↑(toFs k).support ⊆ D := fun d hd => hD₀D (hsupp_sub hd)
      obtain ⟨-, hfibmem⟩ := mem_carryFreeFiber_of_muWeight hf2 hcol
        hsubD' hcard.le hweight hres
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hfibmem, hweight⟩
    · -- restriction lands in the multiplicity-vector filter
      intro φ hφ
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hφ
      obtain ⟨hfibmem, hw⟩ := hφ
      have hsupp_sub : φ.support ⊆ D₀ := support_subset_carryFreeFiberSupport hfibmem
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [sum_apply_superset_cf hsupp_sub]
        exact hfibmem.2.1
      · intro d hd
        exact hsupp_sub (Finsupp.mem_support_iff.mpr hd)
      · rw [muWeight_eq_sum_superset_cf hf2 hsupp_sub]
        exact hw
    · -- left inverse
      intro k hk
      rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
      funext d
      exact htoFs_apply k hk.1.2 d
    · -- right inverse
      intro φ hφ
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hφ
      have hsupp_sub : φ.support ⊆ D₀ := support_subset_carryFreeFiberSupport hφ.1
      ext d
      rw [htoFs]
      simp only [Finsupp.onFinset_apply]
      by_cases h : d ∈ D₀
      · rw [if_pos h]
      · rw [if_neg h]
        exact (Finsupp.notMem_support_iff.mp fun hmem => h (hsupp_sub hmem)).symm
    · -- the summands match
      intro k hk
      rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
      obtain ⟨⟨hsum, hksupp⟩, hw⟩ := hk
      have happ := htoFs_apply k hksupp
      have hfun : ⇑(toFs k) = k := funext happ
      have hsupp_sub : (toFs k).support ⊆ D₀ := Finsupp.support_onFinset_subset
      have hmultN : Nat.multinomial (toFs k).support ⇑(toFs k) =
          Nat.multinomial D₀ k :=
        Nat.multinomial_congr_of_sdiff hsupp_sub
          (fun d hd => by
            rw [← happ d]
            exact Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hd).2)
          (fun d _ => happ d)
      have hprod : ∏ d ∈ (toFs k).support,
          (fhat hf2).coeff (muQFun hf2 d) ^ (toFs k) d =
          ∏ d ∈ D₀, (fhat hf2).coeff (muQFun hf2 d) ^ k d := by
        rw [Finset.prod_congr rfl fun d (_ : d ∈ (toFs k).support) => by rw [happ d]]
        refine Finset.prod_subset hsupp_sub fun d _ hd => ?_
        have h0 : k d = 0 := by
          rw [← happ d]
          exact Finsupp.notMem_support_iff.mp hd
        rw [h0, pow_zero]
      rw [hprod.symm]
      congr 1
      exact_mod_cast congrArg _ hmultN.symm
  rw [hpow_red, htrunc_pow]
  exact hreindex

/-- The **total coset sum** under the collapse hypothesis: the coefficient computation behind
identity (3.6) in the proof of Proposition 3.4, with the leading coefficient `a_n`. For any
finite set `W ⊆ ℤ` containing every `w` at which `P(f̂)` has a nonzero coefficient on the
coset `-‖u‖/T + w/T`, the total `∑_{w ∈ W} p^{w/T} (P(f̂))_{-‖u‖/T + w/T}` equals
`a_n · [X^u] (H_D)^n`, where `[X^u] (H_D)^n` is the sum `S_n(u)` of (3.4). -/
theorem totalSum_eq_carryFree (hD : ∀ d ∈ D, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {n : ℕ} {u : DigitSeries} (hu : u.IsP p) (hcol : IsCollapse (p := p) n D u)
    (P : Polynomial ℤᶜᵘⁿ_[p]) (hdeg : P.natDegree = n)
    {W : Finset ℤ}
    (hW : ∀ w : ℤ, w ∉ W →
      ((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
        (-(u.norm p : ℚ) / (T : ℚ) + (w : ℚ) / (T : ℚ)) = 0) :
    (∑ w ∈ W, pInvTQ p (T : ℕ) ^ w *
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
        (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
          (-(u.norm p : ℚ) / (T : ℚ) + (w : ℚ) / (T : ℚ)))) =
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)]) (OQpCUn_embd p T (P.coeff n)) *
        (DigitCoefficients.power (coefficientFamily p D (adFun hf2)) n) ⟨u, hu⟩ := by
  classical
  set g₀ : ℚ := -(u.norm p : ℚ) / (T : ℚ) with hg₀
  have hTQ : ((T : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr T.ne_zero
  -- the per-coset coefficient formula
  have hcoeff : ∀ w : ℤ,
      ((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff (g₀ + (w : ℚ) / (T : ℚ)) =
        OQpCUn_embd p T (P.coeff n) *
          ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
            if aggWeight hf2 φ = w then
              (Nat.multinomial φ.support φ : ℤᶜᵘⁿ_[p,(T : ℕ)]) *
                ∏ d ∈ φ.support, (fhat hf2).coeff (muQFun hf2 d) ^ φ d
            else 0 := by
    intro w
    set q : ℚ := g₀ + (w : ℚ) / (T : ℚ) with hq
    have hqres : ((T : ℚ) * q + (u.norm p : ℚ)).isInt = true := by
      have heq : (T : ℚ) * q + (u.norm p : ℚ) = ((w : ℤ) : ℚ) := by
        rw [hq, hg₀]
        field_simp
        ring
      rw [heq]
      exact isInt_intCast' w
    have hlow : ∀ i ∈ Finset.range n,
        OQpCUn_embd p T (P.coeff i) * ((fhat hf2) ^ i).coeff q = 0 := by
      intro i hi
      rw [fhat_pow_coeff_eq_zero_of_lt_cf hD hf2 hcol
        (Finset.mem_range.mp hi) hqres, mul_zero]
    rw [aeval_fhat_coeff_eq hf2 P hdeg.le q, Finset.sum_range_succ,
      Finset.sum_eq_zero hlow, zero_add,
      fhat_pow_coeff_eq_sum_carryFreeFiber hD hf2 hcol hqres]
    refine congrArg _ (Finset.sum_congr rfl fun φ hφ => ?_)
    have hφfib : φ ∈ carryFreeFiber n D u := (Set.Finite.mem_toFinset _).mp hφ
    have hsub : ↑φ.support ⊆ D := hφfib.1
    have hcast := aggWeight_cast hf2 hsub
    rw [hφfib.2.2] at hcast
    have hiff : muWeight hf2 φ = q ↔ aggWeight hf2 φ = w := by
      constructor
      · intro h
        have h2 : ((aggWeight hf2 φ : ℤ) : ℚ) = ((w : ℤ) : ℚ) := by
          rw [hcast, h, hq, hg₀]
          field_simp
          ring
        exact_mod_cast h2
      · intro h
        have h2 : (T : ℚ) * muWeight hf2 φ + (u.norm p) = ((w : ℤ) : ℚ) := by
          rw [← hcast, h]
        rw [hq, hg₀]
        field_simp at h2 ⊢
        linarith
    by_cases hcond : muWeight hf2 φ = q
    · rw [if_pos hcond, if_pos (hiff.mp hcond)]
    · rw [if_neg hcond, if_neg fun h => hcond (hiff.mpr h)]
  -- only the fiber weights carry non-zero coefficients
  set Wfin : Finset ℤ :=
    (carryFreeFiber_finite n D u).toFinset.image (fun φ => aggWeight hf2 φ)
    with hWfin
  have hvanish : ∀ w : ℤ, w ∉ Wfin →
      ((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff (g₀ + (w : ℚ) / (T : ℚ)) = 0 := by
    intro w hw
    rw [hcoeff w]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun φ hφ => ?_)
    rw [if_neg fun heq => hw (by
      rw [hWfin]
      exact Finset.mem_image.mpr ⟨φ, hφ, heq⟩)]
  -- regroup the total sum over the carry-free fiber
  have hregroup : (∑ w ∈ Wfin, pInvTQ p (T : ℕ) ^ w *
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
        (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
          (g₀ + (w : ℚ) / (T : ℚ)))) =
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)]) (OQpCUn_embd p T (P.coeff n)) *
        ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
          (Nat.multinomial φ.support φ : ℚᶜᵘⁿ_[p,(T : ℕ)]) *
            ∏ d ∈ φ.support, adFun hf2 d ^ φ d := by
    calc
      (∑ w ∈ Wfin, pInvTQ p (T : ℕ) ^ w *
          algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
            (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
              (g₀ + (w : ℚ) / (T : ℚ))))
        = ∑ w ∈ Wfin, ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
            if aggWeight hf2 φ = w then
              pInvTQ p (T : ℕ) ^ w *
                algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
                  (OQpCUn_embd p T (P.coeff n)) *
                algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
                  ((Nat.multinomial φ.support φ : ℤᶜᵘⁿ_[p,(T : ℕ)]) *
                    ∏ d ∈ φ.support, (fhat hf2).coeff (muQFun hf2 d) ^ φ d)
            else 0 := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hcoeff w, map_mul, map_sum, ← mul_assoc, Finset.mul_sum]
          refine Finset.sum_congr rfl fun φ _ => ?_
          by_cases hcond : aggWeight hf2 φ = w
          · rw [if_pos hcond, if_pos hcond]
          · rw [if_neg hcond, if_neg hcond, map_zero, mul_zero]
      _ = ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
            pInvTQ p (T : ℕ) ^ (aggWeight hf2 φ) *
              algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
                (OQpCUn_embd p T (P.coeff n)) *
              algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
                ((Nat.multinomial φ.support φ : ℤᶜᵘⁿ_[p,(T : ℕ)]) *
                  ∏ d ∈ φ.support, (fhat hf2).coeff (muQFun hf2 d) ^ φ d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun φ hφ => ?_
          rw [Finset.sum_ite_eq, if_pos (by
            rw [hWfin]
            exact Finset.mem_image_of_mem _ hφ)]
      _ = algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
            (OQpCUn_embd p T (P.coeff n)) *
            ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
              (Nat.multinomial φ.support φ : ℚᶜᵘⁿ_[p,(T : ℕ)]) *
                ∏ d ∈ φ.support, adFun hf2 d ^ φ d := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun φ hφ => ?_
          have hφfib : φ ∈ carryFreeFiber n D u := (Set.Finite.mem_toFinset _).mp hφ
          have hsub : ↑φ.support ⊆ D := hφfib.1
          have hkey : pInvTQ p (T : ℕ) ^ (aggWeight hf2 φ) *
              algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
                (∏ d ∈ φ.support, (fhat hf2).coeff (muQFun hf2 d) ^ φ d) =
              ∏ d ∈ φ.support, adFun hf2 d ^ φ d := by
            rw [map_prod]
            unfold aggWeight
            rw [zpow_finset_sum_cf (pInvTQ_ne_zero p T), ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun d hd => ?_
            have hdD : d ∈ D := hsub hd
            rw [map_pow, mul_comm ((φ d : ℤ)) (aggExpFun hf2 d), zpow_mul,
              zpow_natCast, ← mul_pow, adFun_apply_of_mem hf2 hdD]
            congr 1
            unfold ad
            rw [aggExpFun_apply_of_mem hf2 hdD, muQFun_apply_of_mem hf2 hdD]
            congr 1
            exact congrArg _ (fhatCoeff_eq_Cs hf2 (muToStilde hf2 ⟨d, hdD⟩))
          rw [map_mul, map_natCast, ← hkey]
          ring
  -- extend the sum from `Wfin` to `W` via `W ∪ Wfin`
  have hW_ext : (∑ w ∈ W, pInvTQ p (T : ℕ) ^ w *
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
        (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
          (g₀ + (w : ℚ) / (T : ℚ)))) =
      ∑ w ∈ W ∪ Wfin, pInvTQ p (T : ℕ) ^ w *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
          (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
            (g₀ + (w : ℚ) / (T : ℚ))) :=
    Finset.sum_subset Finset.subset_union_left fun w _ hw => by
      rw [hW w hw, map_zero, mul_zero]
  have hWfin_ext : (∑ w ∈ Wfin, pInvTQ p (T : ℕ) ^ w *
      algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
        (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
          (g₀ + (w : ℚ) / (T : ℚ)))) =
      ∑ w ∈ W ∪ Wfin, pInvTQ p (T : ℕ) ^ w *
        algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)])
          (((P.map (OQpCUn_embd p T)).aeval (fhat hf2)).coeff
            (g₀ + (w : ℚ) / (T : ℚ))) :=
    Finset.sum_subset Finset.subset_union_right fun w _ hw => by
      rw [hvanish w hw, map_zero, mul_zero]
  -- identify the fiber sum with the coefficient of `(H_D)^n` at `u`
  have hpow : (DigitCoefficients.power (coefficientFamily p D (adFun hf2)) n) ⟨u, hu⟩ =
      ∑ φ ∈ (carryFreeFiber_finite n D u).toFinset,
        (Nat.multinomial φ.support φ : ℚᶜᵘⁿ_[p,(T : ℕ)]) *
          ∏ d ∈ φ.support, adFun hf2 d ^ φ d := by
    have hsubF : (carryFreeFiber_finite n D u).toFinset ⊆ (powFiber_finite n u).toFinset := by
      intro φ hφ
      rw [Set.Finite.mem_toFinset] at hφ ⊢
      exact carryFreeFiber_subset_powFiber n D u hφ
    have hisP : ∀ φ ∈ (powFiber_finite n u).toFinset, ∀ d ∈ φ.support, d.IsP p := by
      intro φ hφ d hd
      rw [Set.Finite.mem_toFinset] at hφ
      have hle : d ≤ u := by
        refine Finsupp.le_def.mpr fun i => ?_
        have h := Multiplicity.apply_le_total φ hd i
        rw [hφ.2] at h
        exact h
      exact isP_of_le hu hle
    have hext : ∀ φ ∈ (powFiber_finite n u).toFinset, ∀ d ∈ φ.support,
        DigitCoefficients.extendMv (coefficientFamily p D (adFun hf2)) (d) =
          if d ∈ D then adFun hf2 d else 0 := by
      intro φ hφ d hd
      rw [DigitCoefficients.extendMv_apply_of_isP _ (hisP φ hφ d hd), coefficientFamily_apply]
    rw [DigitCoefficients.power_apply, ← Finset.sum_subset hsubF]
    · refine Finset.sum_congr rfl fun φ hφ => ?_
      have hφcf : φ ∈ carryFreeFiber n D u := (Set.Finite.mem_toFinset _).mp hφ
      congr 1
      refine Finset.prod_congr rfl fun d hd => ?_
      rw [hext φ (hsubF hφ) d hd, if_pos (hφcf.1 hd)]
    · intro φ hφ hφn
      have hφpow := hφ
      rw [Set.Finite.mem_toFinset] at hφn hφ
      have hnot : ¬ (↑φ.support ⊆ D) := fun h => hφn ⟨h, hφ.1, hφ.2⟩
      obtain ⟨d, hd, hdD⟩ := Set.not_subset.mp hnot
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := d) hd ?_)
      rw [hext φ hφpow d hd, if_neg hdD]
      exact zero_pow (Finsupp.mem_support_iff.mp hd)
  rw [hW_ext, ← hWfin_ext, hregroup, hpow]

end PAdicOrderType
