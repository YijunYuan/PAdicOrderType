/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Ramified coefficient rings and fields

Adjoining a `T`-th root of `p` to the Witt vectors over the algebraic closure of the residue
field gives a complete discrete valuation ring. Its fraction field is a finite totally
ramified extension of the completed maximal unramified extension of the p-adic numbers.
These are the ring `Z̆_{p,T} = Z̆_p[p^{1/T}]` and the field `Q̆_{p,T} = Q̆_p(p^{1/T})` of
Section 3.1.

## Main definitions

* `PAdicOrderType.RamifiedCoefficients.OQpCUnT`: the ring obtained by adjoining a root of
  `X ^ T - p`.
* `PAdicOrderType.RamifiedCoefficients.QpCUnT`: its fraction field with the discrete valuation.
* `PAdicOrderType.RamifiedCoefficients.pInvTQ`: the chosen uniformizer in the fraction field.
* `PAdicOrderType.RamifiedCoefficients.QpCUn_basis`: the power basis over the unramified field.

## Notation

* `ℤᶜᵘⁿ_[p,T]` denotes the ramified coefficient ring, written `Z̆_{p,T}` in Section 3.1.
* `ℚᶜᵘⁿ_[p,T]` denotes its fraction field, written `Q̆_{p,T}` in Section 3.1.

## Implementation notes

Primality and positivity are supplied by `[Fact (Nat.Prime p)]` and `[NeZero T]`.
The multiplicative valuation of `pInvTQ p T` is `ofAdd (-1)`, so its additive normalization
assigns value `1` to the uniformizer and value `T` to `p`. The valuation of an embedded
unramified element is the `T`-th power of its original multiplicative valuation.
-/

@[expose] public section

namespace PAdicOrderType

open WittVector TrustworthyKedlaya


namespace RamifiedCoefficients

variable (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ) [NeZero T]

/-- The polynomial `X^T - p` over `ℤᶜᵘⁿ_[p]`, used to adjoin a `T`-th root of `p`. -/
noncomputable def TPoly : Polynomial (ℤᶜᵘⁿ_[p]) :=
  Polynomial.X ^ T - Polynomial.C ((p : ℕ) : ℤᶜᵘⁿ_[p])

/-- The integral coefficient ring obtained by adjoining a `T`-th root of `p` to
`ℤᶜᵘⁿ_[p]`, realized as the quotient by `X ^ T - p`. This is the ring `Z̆_{p,T}` of (3.2). -/
abbrev OQpCUnT : Type _ := AdjoinRoot (TPoly p T)

@[inherit_doc] notation "ℤᶜᵘⁿ_[" p "," T "]" => OQpCUnT p T

/-- The canonical root `p^{1/T}` of `X^T - p` inside `ℤᶜᵘⁿ_[p,T]`. -/
noncomputable def pInvT : ℤᶜᵘⁿ_[p,T] := AdjoinRoot.root (TPoly p T)

omit [NeZero T] in
/-- The defining relation `(p^{1/T})^T = p`. -/
lemma pInvT_pow_T :
    (pInvT p T) ^ T =
      (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) := by
  have h := AdjoinRoot.eval₂_root (TPoly p T)
  unfold TPoly at h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact h

/-- `TPoly p T = X^T - C p` is monic. -/
lemma TPoly_monic : (TPoly p T).Monic := by
  unfold TPoly
  exact Polynomial.monic_X_pow_sub_C _ (NeZero.ne T)

omit [NeZero T] in
/-- `TPoly p T` has natural degree `T`. -/
lemma TPoly_natDegree : (TPoly p T).natDegree = T := by
  unfold TPoly; exact Polynomial.natDegree_X_pow_sub_C

/-- `TPoly p T` is Eisenstein at the maximal ideal of `ℤᶜᵘⁿ_[p]`. -/
private lemma TPoly_isEisensteinAt :
    (TPoly p T).IsEisensteinAt (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p])) := by
  have hp_ne : ((p : ℕ) : ℤᶜᵘⁿ_[p]) ≠ 0 := WittVector.p_nonzero p _
  have hT_ne : T ≠ 0 := NeZero.ne T
  have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
      Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
  refine (TPoly_monic p T).isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
  · exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  · intro n hn
    rw [TPoly_natDegree] at hn
    have hcoeff : (TPoly p T).coeff n =
        (if n = T then 1 else 0) - (if n = 0 then ((p : ℕ) : ℤᶜᵘⁿ_[p]) else 0) := by
      unfold TPoly
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rw [hcoeff, hM_eq]
    have hnT : n ≠ T := Nat.ne_of_lt hn
    by_cases hn0 : n = 0
    · subst hn0
      have hT0 : (0 : ℕ) ≠ T := fun h => hT_ne h.symm
      simp only [hT0, if_false, if_true, zero_sub]
      exact (Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])}).neg_mem
        (Ideal.subset_span (Set.mem_singleton _))
    · simp [hnT, hn0]
  · -- coeff 0 of `X^T - C p` is `-p`; show `-p ∉ maximalIdeal^2`.
    have h0 : (TPoly p T).coeff 0 = -((p : ℕ) : ℤᶜᵘⁿ_[p]) := by
      unfold TPoly
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      simp [hT_ne.symm]
    rw [h0]
    intro hmem
    have hmem' : ((p : ℕ) : ℤᶜᵘⁿ_[p]) ∈
        (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p])) ^ 2 := by
      have h := (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) ^ 2).neg_mem hmem
      simpa using h
    rw [hM_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem'
    obtain ⟨r, hr⟩ := hmem'
    -- p = p^2 * r ⇒ p * (1 - p*r) = 0 ⇒ since p ≠ 0, p*r = 1, so p is a unit, contradiction.
    have hzero : ((p : ℕ) : ℤᶜᵘⁿ_[p]) * (1 - ((p : ℕ) : ℤᶜᵘⁿ_[p]) * r) = 0 := by
      have : ((p : ℕ) : ℤᶜᵘⁿ_[p]) - ((p : ℕ) : ℤᶜᵘⁿ_[p]) ^ 2 * r = 0 := by
        rw [← hr]; ring
      linear_combination this
    rcases mul_eq_zero.mp hzero with h | h
    · exact hp_ne h
    · have hpr : ((p : ℕ) : ℤᶜᵘⁿ_[p]) * r = 1 := by
        have hh : 1 - ((p : ℕ) : ℤᶜᵘⁿ_[p]) * r = 0 := h
        linear_combination -hh
      have hunit : IsUnit ((p : ℕ) : ℤᶜᵘⁿ_[p]) :=
        IsUnit.of_mul_eq_one (a := ((p : ℕ) : ℤᶜᵘⁿ_[p])) r hpr
      exact (WittVector.irreducible p).not_isUnit hunit

/-- `TPoly p T` is irreducible. -/
private lemma TPoly_irreducible : Irreducible (TPoly p T) := by
  apply (TPoly_isEisensteinAt p T).irreducible
  · exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  · exact (TPoly_monic p T).isPrimitive
  · rw [TPoly_natDegree]; exact (NeZero.pos T)

/-- `ℤᶜᵘⁿ_[p,T]` is a domain.
The argument: `X^T - p` is Eisenstein at the maximal ideal of the DVR `ℤᶜᵘⁿ_[p]`, hence
irreducible, hence the quotient `AdjoinRoot (X^T - p)` is an integral domain. -/
instance instIsDomainOQpCUnT : IsDomain (ℤᶜᵘⁿ_[p,T]) := by
  apply AdjoinRoot.isDomain_of_prime
  exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp (TPoly_irreducible p T)

/-- `pInvT p T` is nonzero. Proof: `(pInvT)^T = algebraMap p` is nonzero in `S`, since `p` is
nonzero in `R` and `algebraMap` is injective. -/
private lemma pInvT_ne_zero : pInvT p T ≠ 0 := by
  intro h
  have h1 : (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) = 0 := by
    rw [← pInvT_pow_T, h, zero_pow (NeZero.ne T)]
  have hinj : Function.Injective (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree (TPoly_monic p T).ne_zero, TPoly_natDegree]
    exact_mod_cast NeZero.ne T
  have h2 : ((p : ℕ) : ℤᶜᵘⁿ_[p]) = 0 :=
    hinj (by rw [h1, map_zero])
  exact WittVector.p_nonzero p _ h2

/-- The residue map `ρ : ℤᶜᵘⁿ_[p,T] →+* IsLocalRing.ResidueField (ℤᶜᵘⁿ_[p])` obtained
by lifting the quotient `ℤᶜᵘⁿ_[p] →+* (ℤᶜᵘⁿ_[p])/m` along the relation `(pInvT)^T = p`.
Sends `pInvT` to `0`. -/
private noncomputable def TResidue :
    ℤᶜᵘⁿ_[p,T] →+* IsLocalRing.ResidueField (ℤᶜᵘⁿ_[p]) :=
  AdjoinRoot.lift (IsLocalRing.residue (ℤᶜᵘⁿ_[p])) 0 (by
    -- Show `(TPoly p T).eval₂ residue 0 = 0`.
    unfold TPoly
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      zero_pow (NeZero.ne T), zero_sub, neg_eq_zero]
    -- The residue of `p` in the residue field is zero because `p` lies in the max ideal.
    have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
        Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
    change (IsLocalRing.residue (ℤᶜᵘⁿ_[p])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) = 0
    rw [IsLocalRing.residue_eq_zero_iff, hM_eq]
    exact Ideal.subset_span (Set.mem_singleton _))

private lemma TResidue_pInvT : TResidue p T (pInvT p T) = 0 := by
  unfold TResidue pInvT
  exact AdjoinRoot.lift_root _

private lemma TResidue_of (a : ℤᶜᵘⁿ_[p]) :
    TResidue p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) a) =
      IsLocalRing.residue (ℤᶜᵘⁿ_[p]) a := by
  unfold TResidue
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]

/-- The kernel of the residue map equals the principal ideal generated by `pInvT`.
This is the power-basis kernel calculation. -/
private lemma TResidue_eq_zero_iff (x : ℤᶜᵘⁿ_[p,T]) :
    TResidue p T x = 0 ↔ pInvT p T ∣ x := by
  constructor
  · intro hx
    set f := TPoly p T with hf_def
    have hf_monic : f.Monic := TPoly_monic p T
    set q : Polynomial (ℤᶜᵘⁿ_[p]) := AdjoinRoot.modByMonicHom hf_monic x with hq_def
    have hq : AdjoinRoot.mk f q = x := AdjoinRoot.mk_leftInverse hf_monic x
    have hRes : TResidue p T x =
        IsLocalRing.residue (ℤᶜᵘⁿ_[p]) (q.coeff 0) := by
      rw [← hq]
      change AdjoinRoot.lift (IsLocalRing.residue (ℤᶜᵘⁿ_[p])) 0 _ (AdjoinRoot.mk f q) = _
      rw [AdjoinRoot.lift_mk, Polynomial.eval₂_eq_eval_map,
        ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    rw [hRes, IsLocalRing.residue_eq_zero_iff] at hx
    have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
        Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
    rw [hM_eq, Ideal.mem_span_singleton] at hx
    obtain ⟨b, hb⟩ := hx
    have hq_split : Polynomial.X * q.divX + Polynomial.C (q.coeff 0) = q :=
      Polynomial.X_mul_divX_add q
    have hxeq : x = pInvT p T * AdjoinRoot.mk f q.divX +
        algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (q.coeff 0) := by
      conv_lhs => rw [← hq, ← hq_split]
      rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
      rfl
    rw [hxeq, hb]
    have hpπT : algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (((p : ℕ) : ℤᶜᵘⁿ_[p]) * b) =
        (pInvT p T) ^ T * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) b := by
      rw [map_mul]
      congr 1
      exact (pInvT_pow_T p T).symm
    rw [hpπT]
    refine ⟨AdjoinRoot.mk f q.divX +
      (pInvT p T) ^ (T - 1) * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) b, ?_⟩
    have hT_split : (pInvT p T) ^ T = pInvT p T * (pInvT p T) ^ (T - 1) := by
      conv_rhs => rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos T)]
    rw [hT_split]; ring
  · rintro ⟨y, rfl⟩
    rw [map_mul, TResidue_pInvT, zero_mul]

/-- `pInvT p T` is irreducible. -/
private lemma pInvT_irreducible : Irreducible (pInvT p T) := by
  have hπ_ne : pInvT p T ≠ 0 := pInvT_ne_zero p T
  refine ⟨?_, ?_⟩
  · intro hu
    have h0 : TResidue p T (pInvT p T) = 0 := TResidue_pInvT p T
    have hu' : IsUnit (TResidue p T (pInvT p T)) := hu.map _
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  · intro a b hab
    have h0 : TResidue p T (a * b) = 0 := by rw [← hab, TResidue_pInvT]
    rw [map_mul] at h0
    rcases mul_eq_zero.mp h0 with ha0 | hb0
    · obtain ⟨c, rfl⟩ := (TResidue_eq_zero_iff p T a).mp ha0
      have hcb : c * b = 1 := by
        have h1 : pInvT p T * (c * b) = pInvT p T * 1 := by
          rw [mul_one]; linear_combination -hab
        exact mul_left_cancel₀ hπ_ne h1
      have hbc : b * c = 1 := by rw [mul_comm]; exact hcb
      exact Or.inr (IsUnit.of_mul_eq_one c hbc)
    · obtain ⟨c, rfl⟩ := (TResidue_eq_zero_iff p T b).mp hb0
      have hac : a * c = 1 := by
        have h1 : pInvT p T * (a * c) = pInvT p T * 1 := by
          rw [mul_one]; linear_combination -hab
        exact mul_left_cancel₀ hπ_ne h1
      exact Or.inl (IsUnit.of_mul_eq_one c hac)

/-- `(pInvT)` is a maximal ideal: `S/(pInvT) ≅ ResidueField R` is a field. -/
private lemma pInvT_maximal :
    (Ideal.span {pInvT p T} : Ideal (ℤᶜᵘⁿ_[p,T])).IsMaximal := by
  -- The kernel of TResidue equals span {pInvT}, and TResidue is surjective onto a field.
  have hker : RingHom.ker (TResidue p T) = Ideal.span {pInvT p T} := by
    ext x
    rw [RingHom.mem_ker, TResidue_eq_zero_iff, Ideal.mem_span_singleton]
  have hsurj : Function.Surjective (TResidue p T) := by
    intro y
    -- Every element of the residue field is the residue of some r : R; lift via algebraMap.
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) r, ?_⟩
    rw [TResidue_of]; exact hr
  -- S/(pInvT) ≅ ResidueField R via lift.
  have hquot_field :
      (Ideal.span {pInvT p T} : Ideal (ℤᶜᵘⁿ_[p,T])).IsMaximal := by
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective (TResidue p T) hsurj
  exact hquot_field

/-- `ℤᶜᵘⁿ_[p,T]` is a local ring with maximal ideal `(pInvT)`. -/
private lemma instLocalRingOQpCUnT : IsLocalRing (ℤᶜᵘⁿ_[p,T]) := by
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨Ideal.span {pInvT p T}, pInvT_maximal p T, ?_⟩
  intro M hM
  have hint : Algebra.IsIntegral (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) := by
    have := (TPoly_monic p T).finite_adjoinRoot
    exact Algebra.IsIntegral.of_finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
  have hMmax : M.IsMaximal := hM
  have hMcomap_max : (M.comap (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hMcomap_eq : M.comap (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) =
      IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) :=
    IsLocalRing.eq_maximalIdeal hMcomap_max
  have hpR_mem : (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) ∈ M := by
    have : ((p : ℕ) : ℤᶜᵘⁿ_[p]) ∈ M.comap (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) := by
      rw [hMcomap_eq]
      have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
          Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
      rw [hM_eq]; exact Ideal.subset_span (Set.mem_singleton _)
    exact Ideal.mem_comap.mp this
  have hπpow_mem : (pInvT p T) ^ T ∈ M := by
    rw [pInvT_pow_T]; exact hpR_mem
  have hπ_mem : pInvT p T ∈ M := hM.isPrime.mem_of_pow_mem T hπpow_mem
  have hsub : Ideal.span {pInvT p T} ≤ M := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hπ_mem
  exact ((pInvT_maximal p T).eq_of_le hM.ne_top hsub).symm

/-- All elements of a multiset associated to a fixed element have product associated to a power. -/
private lemma _root_.Multiset.prod_assoc_pow {α : Type*} [CommMonoid α] (m : Multiset α) (a : α)
    (h : ∀ q ∈ m, Associated q a) : Associated m.prod (a ^ Multiset.card m) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons q m' ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact (h q (Multiset.mem_cons_self q m')).mul_mul
      (ih (fun r hr => h r (Multiset.mem_cons_of_mem hr)))

/-- Every nonzero `x : ℤᶜᵘⁿ_[p,T]` factors as `(pInvT)^n * u` for some unit `u`.
This is the existence half of `HasUnitMulPowIrreducibleFactorization`. -/
private lemma exists_pInvT_pow_unit_decomposition (x : ℤᶜᵘⁿ_[p,T]) (hx : x ≠ 0) :
    ∃ (n : ℕ), Associated ((pInvT p T) ^ n) x := by
  have : IsLocalRing (ℤᶜᵘⁿ_[p,T]) := instLocalRingOQpCUnT p T
  have : Module.Finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) := (TPoly_monic p T).finite_adjoinRoot
  have : IsNoetherian (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
    isNoetherian_of_isNoetherianRing_of_finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
  have : IsNoetherianRing (ℤᶜᵘⁿ_[p,T]) := by
    refine isNoetherianRing_of_surjective (Polynomial (ℤᶜᵘⁿ_[p])) (ℤᶜᵘⁿ_[p,T])
      (AdjoinRoot.mk (TPoly p T)) ?_
    exact AdjoinRoot.mk_surjective
  have : WfDvdMonoid (ℤᶜᵘⁿ_[p,T]) := IsNoetherianRing.wfDvdMonoid
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  refine ⟨Multiset.card fx, ?_⟩
  have hπ_irr : Irreducible (pInvT p T) := pInvT_irreducible p T
  have hassoc_each : ∀ q ∈ fx, Associated q (pInvT p T) := by
    intro q hq
    have hq_irr : Irreducible q := hfx.1 q hq
    -- q is irreducible, hence not a unit, hence in the unique maximal ideal = span {pInvT}
    have hq_nu : ¬ IsUnit q := hq_irr.not_isUnit
    have hπ_max : (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])) = Ideal.span {pInvT p T} := by
      have hmax := pInvT_maximal p T
      exact (IsLocalRing.eq_maximalIdeal hmax).symm
    have hq_mem : q ∈ Ideal.span {pInvT p T} := by
      rw [← hπ_max]; exact hq_nu
    rw [Ideal.mem_span_singleton] at hq_mem
    obtain ⟨y, hy⟩ := hq_mem
    rcases hq_irr.isUnit_or_isUnit hy with hu | hu
    · exact absurd hu (pInvT_irreducible p T).not_isUnit
    · -- q = pInvT * y, y is a unit, hence Associated q pInvT.
      obtain ⟨v, hv⟩ := hu
      refine ⟨v⁻¹, ?_⟩
      rw [hy, mul_assoc, ← hv, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hprod_assoc : Associated fx.prod ((pInvT p T) ^ (Multiset.card fx)) :=
    Multiset.prod_assoc_pow fx (pInvT p T) hassoc_each
  exact hprod_assoc.symm.trans hfx.2

instance instDVROQpCUnT : IsDiscreteValuationRing (ℤᶜᵘⁿ_[p,T]) := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨pInvT p T, pInvT_irreducible p T, ?_⟩
  intro x hx
  exact exists_pInvT_pow_unit_decomposition p T x hx

/-- The fraction field of `ℤᶜᵘⁿ_[p,T]`, equipped with the discrete valuation whose
uniformizer is the chosen `T`-th root of `p`. This is the field `Q̆_{p,T}` in the proof of
Proposition 3.4.

The `WithVal` wrapper supplies the `Valued` instance with value group
`WithZero (Multiplicative ℤ)`. -/
abbrev QpCUnT : Type _ :=
  WithVal ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation
    (FractionRing (ℤᶜᵘⁿ_[p,T])))

@[inherit_doc] notation "ℚᶜᵘⁿ_[" p "," T "]" => QpCUnT p T

/-- The element `p^{1/T}` viewed inside the fraction field `ℚᶜᵘⁿ_[p,T]`. -/
noncomputable def pInvTQ : ℚᶜᵘⁿ_[p,T] :=
  algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (pInvT p T)

/-- The valuation of the uniformizer `pInvTQ p T` (a `T`-th root of `p`) is `ofAdd(-1)` — the
`T`-scaled analogue of `valued_v_p`. -/
lemma valued_v_pInvT :
    Valued.v (pInvTQ p T) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
  unfold pInvTQ
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal,
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_of_algebraMap]
  have hirr : Irreducible (pInvT p T) := pInvT_irreducible p T
  have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).asIdeal =
      Ideal.span {pInvT p T} := hirr.maximalIdeal_eq
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
    (pInvT_ne_zero p T) hpe]
  rfl

/-- The valuation of `(pInvTQ p T)^n` is `ofAdd(-n)` for integer `n`. -/
lemma valued_v_pInvT_zpow (n : ℤ) :
    Valued.v ((pInvTQ p T) ^ n) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  have hzpow : Valued.v ((pInvTQ p T) ^ n) = (Valued.v (pInvTQ p T)) ^ n :=
    map_zpow₀ Valued.v _ _
  rw [hzpow, valued_v_pInvT, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul n (-1 : ℤ)]
  congr 1
  ring

/-- The open ball `{y | v(y) < c}` is a neighbourhood of `0` in `ℚᶜᵘⁿ_[p,T]` for any nonzero `c` —
the `T`-scaled analogue of `mem_nhds_zero_v_lt`. -/
lemma Tmem_nhds_zero_v_lt {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    {y : ℚᶜᵘⁿ_[p,T] | Valued.v y < c} ∈ nhds (0 : ℚᶜᵘⁿ_[p,T]) := by
  rw [Valued.mem_nhds]
  have hva : Valued.v ((pInvTQ p T) ^ (-(WithZero.log c))) = c := by
    rw [valued_v_pInvT_zpow, neg_neg, ← WithZero.exp_eq_coe_ofAdd, WithZero.exp_log hc]
  have hane : Valued.v.restrict ((pInvTQ p T) ^ (-(WithZero.log c))) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hva]; exact hc
  refine ⟨Units.mk0 (Valued.v.restrict ((pInvTQ p T) ^ (-(WithZero.log c)))) hane, ?_⟩
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, sub_zero, Units.val_mk0,
    Valuation.embedding_restrict, hva] at hy
  exact hy

/-- Every neighbourhood `U` of `0` in `ℚᶜᵘⁿ_[p,T]` contains a valuation ball `{y | v(y) < c}` for
some nonzero `c`. -/
lemma Texists_v_lt_subset {U : Set (ℚᶜᵘⁿ_[p,T])} (hU : U ∈ nhds (0 : ℚᶜᵘⁿ_[p,T])) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ {y : ℚᶜᵘⁿ_[p,T] | Valued.v y < c} ⊆ U := by
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1,
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ, ?_⟩
  intro y hy
  apply hγ
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, sub_zero]
  exact hy

/-- Given a witness `w` with `v(w) = c ≠ 0`, the ball `{y | v(y - x) < c}` is a neighbourhood of
`x` in `ℚᶜᵘⁿ_[p,T]`. -/
lemma Tmem_nhds_v_sub_lt {x w : ℚᶜᵘⁿ_[p,T]} {c : WithZero (Multiplicative ℤ)}
    (hc : c ≠ 0) (hw : Valued.v w = c) :
    {y : ℚᶜᵘⁿ_[p,T] | Valued.v (y - x) < c} ∈ nhds x := by
  rw [Valued.mem_nhds]
  have hane : Valued.v.restrict w ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hw]; exact hc
  refine ⟨Units.mk0 (Valued.v.restrict w) hane, ?_⟩
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, Units.val_mk0,
    Valuation.embedding_restrict, hw] at hy
  exact hy

/-- The natural ring inclusion `ℤᶜᵘⁿ_[p] ↪ ℤᶜᵘⁿ_[p,T]`. -/
noncomputable def OQpCUn_embd : ℤᶜᵘⁿ_[p] →+* ℤᶜᵘⁿ_[p,T] :=
  algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])

/-- The inclusion `ℤᶜᵘⁿ_[p] ↪ ℤᶜᵘⁿ_[p,T]` is injective.  The monic polynomial `X^T - p` has positive
degree, so the quotient algebra is free of rank `T`. -/
lemma OQpCUn_embd_injective : Function.Injective (OQpCUn_embd p T) := by
  unfold OQpCUn_embd
  rw [AdjoinRoot.algebraMap_eq]
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [Polynomial.degree_eq_natDegree (TPoly_monic p T).ne_zero, TPoly_natDegree]
  exact_mod_cast NeZero.ne T

/-- The natural field inclusion `ℚᶜᵘⁿ_[p] ↪ ℚᶜᵘⁿ_[p,T]`, obtained by extending
`OQpCUn_embd` to the fraction fields. -/
noncomputable def QpCUn_embd : ℚᶜᵘⁿ_[p] →+* ℚᶜᵘⁿ_[p,T] :=
  IsFractionRing.lift (A := ℤᶜᵘⁿ_[p]) (K := ℚᶜᵘⁿ_[p]) (L := ℚᶜᵘⁿ_[p,T])
    (g := (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T))
    (((IsFractionRing.injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp
      (OQpCUn_embd_injective p T)))

/-- View `ℚᶜᵘⁿ_[p,T]` as a `ℚᶜᵘⁿ_[p]`-algebra via `QpCUn_embd`. -/
noncomputable instance : Algebra (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) :=
  (QpCUn_embd p T).toAlgebra

/-- The integral inclusion and the fraction-field inclusion form the scalar tower
`ℤᶜᵘⁿ_[p] → ℚᶜᵘⁿ_[p] → ℚᶜᵘⁿ_[p,T]`. -/
instance instIsScalarTowerOQpCUnQpCUnQpCUnT :
    IsScalarTower (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) x =
    QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) x)
  have hL : (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) x =
      (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) (OQpCUn_embd p T x) := by
    rw [show (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) =
        (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T) from ?_]
    · rfl
    · ext y
      change (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) y =
        (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) ((OQpCUn_embd p T) y)
      unfold OQpCUn_embd
      exact IsScalarTower.algebraMap_apply (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) y
  rw [hL]
  rw [show QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) x) =
      ((algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T)) x from
    IsFractionRing.lift_algebraMap _ x]
  rfl

/-- The ramified integral ring is a finite module over `ℤᶜᵘⁿ_[p]`, with the
rank-`T` power basis given by the monic defining polynomial. -/
instance instModuleFiniteOQpCUnT : Module.Finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  (AdjoinRoot.powerBasis' (TPoly_monic p T)).finite

instance instFaithfulSMulOQpCUnT : FaithfulSMul (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (OQpCUn_embd_injective p T)

instance instAlgebraIsAlgebraicOQpCUnT : Algebra.IsAlgebraic (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  Algebra.IsAlgebraic.of_finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])

/-- The ramified fraction field is the localization of `ℤᶜᵘⁿ_[p,T]` at the images
of the nonzero elements of `ℤᶜᵘⁿ_[p]`. -/
instance instIsLocalizationOQpCUnTQpCUnT :
    IsLocalization (Algebra.algebraMapSubmonoid (ℤᶜᵘⁿ_[p,T])
      (nonZeroDivisors (ℤᶜᵘⁿ_[p]))) (ℚᶜᵘⁿ_[p,T]) :=
  Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors _ _ _

/-- The ramified fraction field is a finite-dimensional extension of `ℚᶜᵘⁿ_[p]`.
Localizing the integral power basis gives a basis of size `T`. -/
instance instModuleFiniteQpCUnT : Module.Finite (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) := by
  have hpb : Module.Finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
    (AdjoinRoot.powerBasis' (TPoly_monic p T)).finite
  exact Module.Finite.of_isLocalization (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
    (Rₚ := ℚᶜᵘⁿ_[p]) (Sₚ := ℚᶜᵘⁿ_[p,T]) (nonZeroDivisors (ℤᶜᵘⁿ_[p]))

/-- An integral unit has multiplicative valuation `1` in the ramified fraction field. -/
private lemma Tvalued_v_algebraMap_unit_one (u : (ℤᶜᵘⁿ_[p,T])ˣ) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) = 1 := by
  have h1 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one u.val
  have h2 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one u.inv
  have h3 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) *
            Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, u.val_inv]; simp
  by_contra h_ne_one
  have h1_lt : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) < 1 :=
    lt_of_le_of_ne h1 h_ne_one
  have h_lt : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) *
            Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) < 1 := by
    calc
      Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) ≤
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) * 1 := mul_le_mul' (le_refl _) h2
      _ = Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) := mul_one _
      _ < 1 := h1_lt
  rw [h3] at h_lt
  exact lt_irrefl _ h_lt

/-- Algebra-map square commutativity: viewing `OQpCUn_embd` followed by `algebraMap` to `K`
agrees with `algebraMap` to `K₀` followed by the field inclusion `K₀ ↪ K`. -/
lemma algebraMap_OQpCUn_embd_compat (a : ℤᶜᵘⁿ_[p]) :
    algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (OQpCUn_embd p T a) =
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a) := by
  change algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) a) =
    QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a)
  unfold QpCUn_embd
  exact (IsFractionRing.lift_algebraMap (g :=
    (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T)) _ a).symm

/-- The integer-side valuation identity for the totally ramified extension `K₀ ↪ K`. -/
lemma valued_v_algebraMap_K₀_K_int (a : ℤᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a)) =
      (Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a))^T := by
  rw [← algebraMap_OQpCUn_embd_compat]
  by_cases ha : a = 0
  · subst ha; simp [map_zero, zero_pow (NeZero.ne T)]
  · obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha
      (WittVector.irreducible p)
    obtain ⟨u, hu⟩ := h.symm
    rw [← hu]
    rw [map_mul (OQpCUn_embd p T), map_pow (OQpCUn_embd p T)]
    rw [map_mul, map_pow]
    rw [Valuation.map_mul, Valuation.map_pow]
    rw [show algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (((p : ℕ) : ℤᶜᵘⁿ_[p]) ^ n * u.val) =
          algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (((p : ℕ) : ℤᶜᵘⁿ_[p])) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val from by
      rw [map_mul, map_pow]]
    rw [Valuation.map_mul, Valuation.map_pow]
    have h_unit_K : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        (OQpCUn_embd p T u.val)) = 1 := by
      have hunit : IsUnit (OQpCUn_embd p T u.val) :=
        (OQpCUn_embd p T).isUnit_map u.isUnit
      obtain ⟨v, hv⟩ := hunit
      rw [← hv]
      exact Tvalued_v_algebraMap_unit_one (p := p) (T := T) v
    have h_unit_K0 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) = 1 := by
      have h1 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_le_one u.val
      have h2 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_le_one u.inv
      have h3 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, u.val_inv, map_one, Valuation.map_one]
      have hpos : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at h3
        exact zero_ne_one h3
      exact le_antisymm h1 (by
        rcases (eq_or_lt_of_le h1) with hEq | hLt
        · exact le_of_eq hEq.symm
        · exfalso
          have hprod : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) *
              Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) < 1 :=
            mul_lt_one_of_lt_of_le hLt h2
          rw [h3] at hprod
          exact lt_irrefl _ hprod)
    rw [h_unit_K, h_unit_K0, mul_one, mul_pow, one_pow, mul_one, ← pow_mul]
    have hLHS : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (OQpCUn_embd p T ((p : ℕ) : ℤᶜᵘⁿ_[p]))) =
        ((Multiplicative.ofAdd (-(T : ℤ)) : Multiplicative ℤ) : WithZero _) := by
      rw [show OQpCUn_embd p T ((p : ℕ) : ℤᶜᵘⁿ_[p]) = (pInvT p T) ^ T from
            (pInvT_pow_T p T).symm]
      rw [map_pow]
      rw [show algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (pInvT p T) = pInvTQ p T from rfl]
      rw [show ((pInvTQ p T) ^ T) = ((pInvTQ p T) ^ ((T : ℤ))) by rfl]
      exact valued_v_pInvT_zpow (p := p) (T := T) (T : ℤ)
    have hRHS : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
      rw [QpCUn.valued_algebraMap]
      have hirr : Irreducible ((p : ℕ) : ℤᶜᵘⁿ_[p]) := WittVector.irreducible p
      have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).asIdeal =
          Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := hirr.maximalIdeal_eq
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
        (WittVector.p_nonzero p _) hpe]
      rfl
    rw [hLHS, hRHS, ← WithZero.coe_pow, ← WithZero.coe_pow]
    congr 1
    rw [← ofAdd_nsmul, ← ofAdd_nsmul]
    congr 1
    ring_nf
    rw [mul_comm]

/-- The ramification-index valuation identity `v_K(ι̃ z) = (v_{K₀}(z))^T`. -/
lemma valued_v_algebraMap_K₀_K (z : ℚᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) z) = (Valued.v z)^T := by
  obtain ⟨a, b, _, hz⟩ := IsFractionRing.div_surjective (A := ℤᶜᵘⁿ_[p]) z
  rw [← hz]
  simp only [map_div₀, div_pow]
  rw [valued_v_algebraMap_K₀_K_int, valued_v_algebraMap_K₀_K_int]

/-- The algebra map `K₀ ↪ K` is continuous at `0`. -/
private lemma tendsto_algebraMap_K₀_K_zero :
    Filter.Tendsto (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) (nhds 0) (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero (ℚᶜᵘⁿ_[p,T]) _).tendsto_right_iff]
  intro γ _
  -- In v4.31 `γ : (ValueGroup₀ Valued.v)ˣ`; work with its `WithZero (Multiplicative ℤ)` image.
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc_ne : c ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  set γ_m : Multiplicative ℤ := WithZero.unzero hc_ne with hγ_m_def
  set n : ℤ := Multiplicative.toAdd γ_m with hn_def
  set k : ℤ := min (n - 1) (-1) with hk_def
  have hk_lt_n : k ≤ n - 1 := min_le_left _ _
  have hT_pos : 0 < (T : ℤ) := by exact_mod_cast Nat.pos_of_neZero T
  have hkT : k * T < n := by
    have h1 : k * T ≤ k * 1 := by
      apply mul_le_mul_of_nonpos_left
      · exact_mod_cast hT_pos
      · linarith [min_le_right (n - 1) (-1)]
    have h2 : k * 1 = k := mul_one _
    linarith
  -- Source bound: the ball `{z | Valued.v z < ofAdd k}` on `ℚᶜᵘⁿ_[p]`.
  rw [Filter.eventually_iff]
  have hsrc : {z : ℚᶜᵘⁿ_[p] | Valued.v z <
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _)} ∈ nhds (0 : ℚᶜᵘⁿ_[p]) :=
    mem_nhds_zero_v_lt WithZero.coe_ne_zero
  refine Filter.mem_of_superset hsrc ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  -- Goal: `Valued.v.restrict (algebraMap z) < γ.1`, i.e. `Valued.v (algebraMap z) < c`.
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc_def, valued_v_algebraMap_K₀_K]
  have hc_eq : c = ((γ_m : Multiplicative ℤ) : WithZero _) :=
    (WithZero.coe_unzero hc_ne).symm
  have hγm_eq : γ_m = Multiplicative.ofAdd n := rfl
  calc (Valued.v z)^T
      ≤ (((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _))^T := by
        apply pow_le_pow_left₀ _ (le_of_lt hz)
        exact zero_le (a := Valued.v z)
    _ < c := by
        rw [← WithZero.coe_pow]
        rw [show ((Multiplicative.ofAdd k : Multiplicative ℤ)^T : Multiplicative ℤ) =
              Multiplicative.ofAdd (k * T) from by
          rw [← ofAdd_nsmul]; congr 1; ring]
        rw [hc_eq, hγm_eq, WithZero.coe_lt_coe]
        exact Multiplicative.ofAdd_lt.mpr hkT

/-- Continuity of `algebraMap K₀ → K`. -/
lemma continuous_algebraMap_K₀_K :
    Continuous (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) := by
  have h0 : ContinuousAt (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) 0 := by
    rw [ContinuousAt, map_zero]
    exact tendsto_algebraMap_K₀_K_zero p T
  exact continuous_of_continuousAt_zero
    (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])).toAddMonoidHom h0

noncomputable instance :
    (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] (WithZero (Multiplicative ℤ))).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation
        (FractionRing (ℤᶜᵘⁿ_[p,T]))).IsRankOneDiscrete := inferInstance
    obtain ⟨γ, hγ, hγ1⟩ := h.exists_generator_lt_one'
    exact ⟨γ, by rw [WithVal.valueGroup_eq]; exact hγ, hγ1⟩

noncomputable instance :
  Valuation.RankOne (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] (WithZero (Multiplicative ℤ))) :=
  Valuation.IsRankOneDiscrete.rankOne
    (v := (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] (WithZero (Multiplicative ℤ))))
    (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt : (1 : NNReal) < (p : NNReal))

noncomputable instance : NontriviallyNormedField ℚᶜᵘⁿ_[p,T] :=
  Valued.toNontriviallyNormedField (ℚᶜᵘⁿ_[p,T]) (WithZero (Multiplicative ℤ))

lemma Texists_lift_of_valued_le_one {z : ℚᶜᵘⁿ_[p,T]} (hz : Valued.v z ≤ 1) :
    ∃ a : ℤᶜᵘⁿ_[p,T], algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a = z := by
  have hz' : ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation
      ((FractionRing (ℤᶜᵘⁿ_[p,T])))) (WithVal.equiv _ z) ≤ 1 := by
    rw [WithVal.val_apply_equiv]; exact hz
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
    (A := ℤᶜᵘⁿ_[p,T]) (K := FractionRing (ℤᶜᵘⁿ_[p,T])) hz'
  refine ⟨a, ?_⟩
  apply (WithVal.equiv _).injective
  rw [WithVal.algebraMap_right_apply] at *
  simpa [WithVal.equiv] using ha

instance : ContinuousSMul (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) :=
    continuousSMul_of_algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (continuous_algebraMap_K₀_K p T)

/-- The `Valued`-induced topology on `ℚᶜᵘⁿ_[p,T]` is complete.

Discharged via `FiniteDimensional.complete` over the finite extension
`ℚᶜᵘⁿ_[p,T] / ℚᶜᵘⁿ_[p]`.  We first view both fields as rank-one nonarchimedean
normed fields using their `Valued` structures, then obtain `ContinuousSMul`
from `isModuleTopologyOfFiniteDimensional`. -/
instance instCompleteSpaceQpCUnT : CompleteSpace (ℚᶜᵘⁿ_[p,T]) :=
  FiniteDimensional.complete (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])

/-- Reindexed `R₀`-power-basis of `ℤᶜᵘⁿ_[p,T]`: the basis `{1, π, …, π^(T-1)}` indexed by
`Fin T` (rather than `Fin (TPoly p T).natDegree`). -/
noncomputable def OQpCUn_basis :
    Module.Basis (Fin T) (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  ((AdjoinRoot.powerBasis' (TPoly_monic p T)).basis).reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, TPoly_natDegree]))

private lemma OQpCUn_basis_apply (i : Fin T) :
    OQpCUn_basis p T i = (pInvT p T) ^ (i.val : ℕ) := by
  unfold OQpCUn_basis
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- The `T`-th power of the uniformizer is the image of `p` in the ramified
fraction field. -/
private lemma pInvTQ_pow_T :
    (pInvTQ p T) ^ T =
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p])) := by
  unfold pInvTQ
  rw [← map_pow, pInvT_pow_T]

/-- The power basis `1, π, …, π ^ (T - 1)` of `ℚᶜᵘⁿ_[p,T]` over `ℚᶜᵘⁿ_[p]`,
where `π` is the chosen `T`-th root of `p`. It is obtained by localizing the integral basis. -/
noncomputable def QpCUn_basis :
    Module.Basis (Fin T) (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) :=
  (OQpCUn_basis p T).localizationLocalization
    (Rₛ := ℚᶜᵘⁿ_[p]) (Aₛ := ℚᶜᵘⁿ_[p,T]) (S := nonZeroDivisors (ℤᶜᵘⁿ_[p]))

private lemma QpCUn_basis_apply (i : Fin T) :
    QpCUn_basis p T i = (pInvTQ p T) ^ (i.val : ℕ) := by
  unfold QpCUn_basis
  rw [Module.Basis.localizationLocalization_apply, OQpCUn_basis_apply]
  unfold pInvTQ
  rw [map_pow]

/-- `K₀`-coordinate projection on the `i`-th basis vector of the `K₀`-power-basis of `K`. -/
noncomputable def QpCUn_proj (i : Fin T) :
    ℚᶜᵘⁿ_[p,T] →ₗ[ℚᶜᵘⁿ_[p]] ℚᶜᵘⁿ_[p] :=
  (QpCUn_basis p T).coord i

private lemma QpCUn_basis_decomp (c : ℚᶜᵘⁿ_[p,T]) :
    c = ∑ i : Fin T, (pInvTQ p T) ^ (i.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i c) := by
  have h := (QpCUn_basis p T).sum_repr c
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [QpCUn_basis_apply, Algebra.smul_def, mul_comm]
  rfl

lemma QpCUn_proj_sum (a : Fin T → ℚᶜᵘⁿ_[p]) (j : Fin T) :
    QpCUn_proj p T j (∑ i : Fin T, (pInvTQ p T) ^ (i.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (a i)) = a j := by
  have h : (∑ i : Fin T, (pInvTQ p T) ^ (i.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (a i)) =
      ∑ i : Fin T, (a i) • (QpCUn_basis p T i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [QpCUn_basis_apply, Algebra.smul_def, mul_comm]
  rw [h]
  unfold QpCUn_proj
  rw [map_sum, Finset.sum_eq_single j]
  · rw [LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp
  · intros i _ hij
    rw [LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [hij]
  · intro h0; exact absurd (Finset.mem_univ _) h0

/-- `pInvTQ` is nonzero — used for `zpow` arithmetic on negative exponents. -/
lemma pInvTQ_ne_zero : (pInvTQ p T) ≠ 0 := by
  change (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) (pInvT p T) ≠ 0
  intro h
  have hinj := FaithfulSMul.algebraMap_injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
  exact pInvT_ne_zero p T (hinj (by rw [h, map_zero]))

/-- `(pInvTQ)^T` equals the image of `(p : ℚᶜᵘⁿ_[p])` in `K`. -/
private lemma pInvTQ_pow_T_K :
    (pInvTQ p T) ^ T =
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])) := by
  rw [pInvTQ_pow_T]
  exact algebraMap_OQpCUn_embd_compat p T _

lemma pInvTQ_pow_T_zmul (m : ℤ) :
    (pInvTQ p T) ^ ((T : ℤ) * m) =
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ m) := by
  have hp_K0 : ((p : ℕ) : ℚᶜᵘⁿ_[p]) =
      algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p]) := by simp
  rw [hp_K0, map_zpow₀, ← pInvTQ_pow_T_K]
  -- Goal: pInvTQ ^ (T * m) = (pInvTQ ^ T) ^ m
  rw [zpow_mul, zpow_natCast]

private lemma valued_v_QpCUn_proj_term_le (c : ℚᶜᵘⁿ_[p,T]) (j : Fin T) :
    Valued.v ((pInvTQ p T) ^ (j.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T j c)) ≤ Valued.v c := by
  -- Notation: term_i := pInvTQ^i * algMap (QpCUn_proj i c).
  let term : Fin T → ℚᶜᵘⁿ_[p,T] := fun i =>
    (pInvTQ p T) ^ (i.val : ℕ) *
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i c)
  change Valued.v (term j) ≤ Valued.v c
  have h_decomp : c = ∑ i : Fin T, term i := QpCUn_basis_decomp p T c
  -- If term j = 0, the bound is trivial.
  by_cases hj : term j = 0
  · rw [hj, Valuation.map_zero]; exact zero_le (a := Valued.v c)
  classical
  let supp : Finset (Fin T) := (Finset.univ.filter (fun i => term i ≠ 0))
  have hj_supp : j ∈ supp := by simp [supp, hj]
  have h_mem_supp : ∀ {i}, i ∈ supp ↔ term i ≠ 0 := by
    intro i; simp [supp]
  -- Pairwise distinct valuations on supp, via the mod-T argument.
  have h_distinct : ∀ i₁ ∈ supp, ∀ i₂ ∈ supp, i₁ ≠ i₂ →
      Valued.v (term i₁) ≠ Valued.v (term i₂) := by
    intro i₁ hi₁ i₂ hi₂ h_ne
    have hterm₁_ne : term i₁ ≠ 0 := h_mem_supp.mp hi₁
    have hterm₂_ne : term i₂ ≠ 0 := h_mem_supp.mp hi₂
    -- term i = pInvTQ^i * algMap (QpCUn_proj i c)
    have hpInvTQ_ne : (pInvTQ p T) ≠ 0 := pInvTQ_ne_zero p T
    have hpInvTQ_pow_ne : ∀ k : ℕ, ((pInvTQ p T) ^ k) ≠ 0 := fun k =>
      pow_ne_zero k hpInvTQ_ne
    have h_a₁_ne : QpCUn_proj p T i₁ c ≠ 0 := by
      intro h0
      apply hterm₁_ne
      change (pInvTQ p T) ^ (i₁.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₁ c) = 0
      rw [h0, map_zero, mul_zero]
    have h_a₂_ne : QpCUn_proj p T i₂ c ≠ 0 := by
      intro h0
      apply hterm₂_ne
      change (pInvTQ p T) ^ (i₂.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₂ c) = 0
      rw [h0, map_zero, mul_zero]
    -- v(QpCUn_proj i_k c) ≠ 0
    have h_v_a_ne₁ : Valued.v (QpCUn_proj p T i₁ c) ≠ 0 := by
      intro h0
      apply h_a₁_ne
      exact (Valuation.zero_iff _).1 h0
    have h_v_a_ne₂ : Valued.v (QpCUn_proj p T i₂ c) ≠ 0 := by
      intro h0
      apply h_a₂_ne
      exact (Valuation.zero_iff _).1 h0
    -- Express valuations via Helper 1A.
    have h_alg_eq₁ : Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (QpCUn_proj p T i₁ c)) = (Valued.v (QpCUn_proj p T i₁ c))^T :=
      valued_v_algebraMap_K₀_K p T _
    have h_alg_eq₂ : Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (QpCUn_proj p T i₂ c)) = (Valued.v (QpCUn_proj p T i₂ c))^T :=
      valued_v_algebraMap_K₀_K p T _
    have h_pInvTQ₁ : Valued.v ((pInvTQ p T) ^ (i₁.val : ℕ)) =
        ((Multiplicative.ofAdd (-(i₁.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [show ((pInvTQ p T) ^ (i₁.val : ℕ)) = ((pInvTQ p T) ^ ((i₁.val : ℤ))) by rfl]
      exact valued_v_pInvT_zpow (p := p) (T := T) (i₁.val : ℤ)
    have h_pInvTQ₂ : Valued.v ((pInvTQ p T) ^ (i₂.val : ℕ)) =
        ((Multiplicative.ofAdd (-(i₂.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [show ((pInvTQ p T) ^ (i₂.val : ℕ)) = ((pInvTQ p T) ^ ((i₂.val : ℤ))) by rfl]
      exact valued_v_pInvT_zpow (p := p) (T := T) (i₂.val : ℤ)
    intro h_eq
    -- Unfold term and apply valuation calculations.
    have h_v_term₁ : Valued.v (term i₁) =
        ((Multiplicative.ofAdd (-(i₁.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) * (Valued.v (QpCUn_proj p T i₁ c))^T := by
      change Valued.v ((pInvTQ p T) ^ (i₁.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₁ c)) = _
      rw [Valuation.map_mul, h_pInvTQ₁, h_alg_eq₁]
    have h_v_term₂ : Valued.v (term i₂) =
        ((Multiplicative.ofAdd (-(i₂.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) * (Valued.v (QpCUn_proj p T i₂ c))^T := by
      change Valued.v ((pInvTQ p T) ^ (i₂.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₂ c)) = _
      rw [Valuation.map_mul, h_pInvTQ₂, h_alg_eq₂]
    rw [h_v_term₁, h_v_term₂] at h_eq
    set m₁ : ℤ := Multiplicative.toAdd (WithZero.unzero h_v_a_ne₁) with hm₁_def
    set m₂ : ℤ := Multiplicative.toAdd (WithZero.unzero h_v_a_ne₂) with hm₂_def
    have hva₁ : Valued.v (QpCUn_proj p T i₁ c) =
        ((Multiplicative.ofAdd m₁ : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [hm₁_def]; simp [WithZero.coe_unzero h_v_a_ne₁]
    have hva₂ : Valued.v (QpCUn_proj p T i₂ c) =
        ((Multiplicative.ofAdd m₂ : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [hm₂_def]; simp [WithZero.coe_unzero h_v_a_ne₂]
    rw [hva₁, hva₂] at h_eq
    rw [← WithZero.coe_pow, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_mul,
      WithZero.coe_inj, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_add,
      Multiplicative.ofAdd.injective.eq_iff] at h_eq
    -- h_eq : -i₁ + T • m₁ = -i₂ + T • m₂
    have h_sub : (T : ℤ) * m₁ - (T : ℤ) * m₂ = (i₁.val : ℤ) - (i₂.val : ℤ) := by
      have h_smul₁ : (T : ℕ) • m₁ = (T : ℤ) * m₁ := by simp
      have h_smul₂ : (T : ℕ) • m₂ = (T : ℤ) * m₂ := by simp
      linarith [h_eq, h_smul₁, h_smul₂]
    have hT_pos : (0 : ℤ) < T := by exact_mod_cast Nat.pos_of_neZero T
    have hT_dvd : (T : ℤ) ∣ (i₁.val : ℤ) - (i₂.val : ℤ) := by
      rw [← h_sub]
      refine ⟨m₁ - m₂, ?_⟩
      ring
    have h_lt₁ : (i₁.val : ℤ) < T := by exact_mod_cast i₁.isLt
    have h_lt₂ : (i₂.val : ℤ) < T := by exact_mod_cast i₂.isLt
    have h_nn₁ : (0 : ℤ) ≤ i₁.val := Int.natCast_nonneg _
    have h_nn₂ : (0 : ℤ) ≤ i₂.val := Int.natCast_nonneg _
    have h_val_eq : i₁.val = i₂.val := by
      obtain ⟨q, hq⟩ := hT_dvd
      have h_q_zero : q = 0 := by nlinarith [sq_nonneg q]
      have : (i₁.val : ℤ) = (i₂.val : ℤ) := by
        rw [h_q_zero, mul_zero] at hq; omega
      exact_mod_cast this
    exact h_ne (Fin.ext h_val_eq)
  -- Apply strict ultrametric: identify the term with maximum valuation, restricted to supp.
  have h_supp_ne : supp.Nonempty := ⟨j, hj_supp⟩
  obtain ⟨k, hk_supp, hk_max⟩ := supp.exists_max_image (fun i => Valued.v (term i)) h_supp_ne
  have h_lt_max : ∀ i ∈ supp, i ≠ k → Valued.v (term i) < Valued.v (term k) := by
    intro i hi hik
    rcases lt_or_eq_of_le (hk_max i hi) with hlt | heq
    · exact hlt
    · exact absurd heq (h_distinct i hi k hk_supp hik)
  have h_decomp_supp : ∑ i : Fin T, term i = ∑ i ∈ supp, term i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi_notin
    by_contra h_ne_zero
    apply hi_notin
    exact h_mem_supp.mpr h_ne_zero
  have h_v_c : Valued.v c = Valued.v (term k) := by
    rw [h_decomp, h_decomp_supp]
    refine Valuation.map_sum_eq_of_lt _ hk_supp ?_
    intro i hi_diff
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi_diff
    exact h_lt_max i hi_diff.1 hi_diff.2
  rw [h_v_c]
  exact hk_max j hj_supp

private lemma tendsto_QpCUn_proj_zero (j : Fin T) :
    Filter.Tendsto (QpCUn_proj p T j) (nhds (0 : ℚᶜᵘⁿ_[p,T])) (nhds (0 : ℚᶜᵘⁿ_[p])) := by
  rw [(Valued.hasBasis_nhds_zero (ℚᶜᵘⁿ_[p]) _).tendsto_right_iff]
  intro γ' _
  -- v4.31: `γ' : (ValueGroup₀ Valued.v)ˣ` on the `K₀` side; use its `WithZero` image.
  set c' : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ'.1 with hc'_def
  have hc'_ne : c' ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ'
  set γ'_m : Multiplicative ℤ := WithZero.unzero hc'_ne with hγ'_m_def
  set N : ℤ := Multiplicative.toAdd γ'_m with hN_def
  -- Choose k = N * T - j.val - 1 (so k + j.val + 1 ≤ N * T, i.e., k + j < N*T).
  set k : ℤ := N * T - (j.val : ℤ) - 1 with hk_def
  have hT_pos : (0 : ℤ) < T := by exact_mod_cast Nat.pos_of_neZero T
  -- Source ball on `K` side, with cutoff `ofAdd k`.
  rw [Filter.eventually_iff]
  have hsrc : {c : ℚᶜᵘⁿ_[p,T] | Valued.v c <
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _)} ∈ nhds (0 : ℚᶜᵘⁿ_[p,T]) :=
    Tmem_nhds_zero_v_lt p T WithZero.coe_ne_zero
  refine Filter.mem_of_superset hsrc ?_
  intro c hc
  simp only [Set.mem_ofPred_eq] at hc ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc'_def]
  -- We have hc : v(c) < ofAdd k.
  -- Goal: v(QpCUn_proj j c) < c' = ofAdd N.
  have h_term_le : Valued.v ((pInvTQ p T) ^ (j.val : ℕ) *
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T j c)) ≤ Valued.v c :=
    valued_v_QpCUn_proj_term_le p T c j
  -- Compute v(pInvTQ^j) = ofAdd(-j).
  have h_pInvTQ_j : Valued.v ((pInvTQ p T) ^ (j.val : ℕ)) =
      ((Multiplicative.ofAdd (-(j.val : ℤ)) : Multiplicative ℤ) : WithZero _) := by
    rw [show ((pInvTQ p T) ^ (j.val : ℕ)) = ((pInvTQ p T) ^ ((j.val : ℤ))) by rfl]
    exact valued_v_pInvT_zpow (p := p) (T := T) (j.val : ℤ)
  rw [Valuation.map_mul, h_pInvTQ_j, valued_v_algebraMap_K₀_K] at h_term_le
  -- h_term_le : ofAdd(-j) * v(QpCUn_proj j c)^T ≤ v(c) < ofAdd k.
  have h_combined :
      ((Multiplicative.ofAdd (-(j.val : ℤ)) : Multiplicative ℤ) : WithZero _) *
        (Valued.v (QpCUn_proj p T j c))^T <
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _) :=
    lt_of_le_of_lt h_term_le hc
  -- Multiply both sides by ofAdd j: v(QpCUn_proj j c)^T < ofAdd(k + j).
  have h_pow_lt : (Valued.v (QpCUn_proj p T j c))^T <
      ((Multiplicative.ofAdd (k + (j.val : ℤ)) : Multiplicative ℤ) : WithZero _) := by
    have hofAdd_j_pos : (0 : WithZero (Multiplicative ℤ)) <
        ((Multiplicative.ofAdd ((j.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      exact WithZero.zero_lt_coe _
    have h_mul := strictMono_mul_left_of_pos hofAdd_j_pos h_combined
    -- Simplify LHS: ofAdd(j) * (ofAdd(-j) * v^T) = v^T.
    have h_simpL : ((Multiplicative.ofAdd ((j.val : ℤ)) : Multiplicative ℤ) : WithZero _) *
        (((Multiplicative.ofAdd (-(j.val : ℤ)) : Multiplicative ℤ) : WithZero _) *
          (Valued.v (QpCUn_proj p T j c))^T) =
        (Valued.v (QpCUn_proj p T j c))^T := by
      rw [← mul_assoc]
      rw [← WithZero.coe_mul, ← ofAdd_add]
      simp
    -- Simplify RHS: ofAdd(j) * ofAdd(k) = ofAdd(j + k).
    have h_simpR : ((Multiplicative.ofAdd ((j.val : ℤ)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) *
        ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
        ((Multiplicative.ofAdd (k + (j.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.coe_mul, ← ofAdd_add]
      congr 1
      rw [add_comm]
    simp only [] at h_mul
    rw [h_simpL, h_simpR] at h_mul
    exact h_mul
  -- Now v^T < ofAdd(k + j) ≤ ofAdd(N*T - 1) < ofAdd(N*T) = (ofAdd N)^T = γ'^T.
  have h_kj_lt : k + (j.val : ℤ) < N * T := by
    rw [hk_def]; linarith
  have h_pow_lt_NT : (Valued.v (QpCUn_proj p T j c))^T <
      ((Multiplicative.ofAdd (N * T) : Multiplicative ℤ) : WithZero _) := by
    apply lt_of_lt_of_le h_pow_lt
    rw [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
    linarith
  -- Convert to v < ofAdd N.
  have h_RHS_eq : ((Multiplicative.ofAdd (N * T) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      (((Multiplicative.ofAdd N : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)))^T := by
    rw [← WithZero.coe_pow, ← ofAdd_nsmul]
    congr 1
    simp only [Int.nsmul_eq_mul, EmbeddingLike.apply_eq_iff_eq]
    ring
  rw [h_RHS_eq] at h_pow_lt_NT
  have h_rhs_pos : (0 : WithZero (Multiplicative ℤ)) <
      ((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    WithZero.zero_lt_coe _
  have h_lt : Valued.v (QpCUn_proj p T j c) <
      ((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero _) := by
    have hT_ne : T ≠ 0 := NeZero.ne T
    by_contra h_not_lt
    push Not at h_not_lt
    have h_pow_le : (((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero _))^T ≤
        (Valued.v (QpCUn_proj p T j c))^T :=
      pow_le_pow_left₀ (le_of_lt h_rhs_pos) h_not_lt T
    exact absurd (lt_of_lt_of_le h_pow_lt_NT h_pow_le) (lt_irrefl _)
  -- Convert c' to ofAdd N.
  have hc'_eq : c' = ((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero _) := by
    rw [hN_def, hγ'_m_def]
    simp [WithZero.coe_unzero hc'_ne]
  rw [hc'_eq]
  exact h_lt

lemma continuous_QpCUn_proj (j : Fin T) :
    Continuous (QpCUn_proj p T j) := by
  have h0 : ContinuousAt (QpCUn_proj p T j) 0 := by
    rw [ContinuousAt, map_zero]
    exact tendsto_QpCUn_proj_zero p T j
  exact continuous_of_continuousAt_zero (QpCUn_proj p T j).toAddMonoidHom h0

end RamifiedCoefficients

end PAdicOrderType
