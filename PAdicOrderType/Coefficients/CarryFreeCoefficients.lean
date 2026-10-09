/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Digits.DigitSeries
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Finite carry-free coefficients

Digit vectors are finitely supported functions `DigitSeries := ℕ+ →₀ ℕ`, with
norm `‖d‖ = ∑ dᵢ p^{-i}`. Proper digit vectors satisfy `DigitSeries.IsP p`.

`Multiplicity.card` and `Multiplicity.total` give the size and weighted sum of a
multiplicity function. The finite power fibers index the multinomial expansion
of finite convolution sums of coefficient functions on proper digit vectors.
`PAdicOrderType.DigitCoefficients.power` computes the finite sum over ordered tuples
whose coordinatewise digit sum is the prescribed proper vector. For the coefficients `A_d`
of (3.2), this is the carry-free sum `S_n(u)` of (3.4).

## Implementation notes

Convolution is defined only at proper digit vectors. The coefficient families carry explicit
convolution and power operations; the multinomial formula is proved using multivariate
power series.
-/

namespace PAdicOrderType



namespace Multiplicity

/-- `|φ|`: the total multiplicity of a finitely supported `φ : DigitSeries →₀ ℕ`. A multiplicity
function *on `D`* satisfies `↑φ.support ⊆ D`. -/
def card (φ : DigitSeries →₀ ℕ) : ℕ :=
  φ.sum fun _ v => v

/-- `Σ(φ)`: the weighted digit-vector sum of a multiplicity function. -/
noncomputable def total (φ : DigitSeries →₀ ℕ) : DigitSeries :=
  φ.sum fun d v => v • d

lemma card_eq_sum (φ : DigitSeries →₀ ℕ) :
    card φ = ∑ d ∈ φ.support, φ d := rfl

lemma total_eq_sum (φ : DigitSeries →₀ ℕ) :
    total φ = ∑ d ∈ φ.support, φ d • d := rfl

/-- `‖Σ(φ)‖ = ∑_{d} φ(d) · ‖d‖`: the norm of the weighted sum. -/
lemma norm_total (p : ℕ) [Fact (Nat.Prime p)] (φ : DigitSeries →₀ ℕ) :
    (total φ).norm p = ∑ d ∈ φ.support, (φ d : ℚ) * d.norm p := by
  rw [total_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun d _ => by
    rw [AddMonoidHom.map_nsmul, nsmul_eq_mul]

end Multiplicity

open Multiplicity

/-! ### Finite multiplicity fibers -/

namespace Multiplicity

/-- The value of `Σ(φ)` at a position `i`. -/
lemma total_apply (φ : DigitSeries →₀ ℕ) (i : ℕ+) :
    total φ i = ∑ d ∈ φ.support, φ d * d i := by
  have := map_sum (Finsupp.applyAddHom i) (fun d => φ d • d) φ.support
  rw [total_eq_sum]
  exact this.trans (Finset.sum_congr rfl fun d _ => rfl)

/-- Every digit vector in the support of `φ` is dominated pointwise by `Σ(φ)`. -/
lemma apply_le_total (φ : DigitSeries →₀ ℕ) {d : DigitSeries}
    (hd : d ∈ φ.support) (i : ℕ+) : d i ≤ total φ i := by
  rw [total_apply]
  calc
    d i ≤ φ d * d i :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hd))
    _ ≤ ∑ e ∈ φ.support, φ e * e i :=
        Finset.single_le_sum (f := fun e => φ e * e i) (fun e _ => Nat.zero_le _) hd

end Multiplicity

/-- The set of digit series dominated pointwise by `u` is finite. -/
lemma finite_setOf_apply_le (u : DigitSeries) :
    {d : DigitSeries | ∀ i, d i ≤ u i}.Finite :=
  Set.finite_Iic u

/-- The **power fiber**: the multiplicity functions of total multiplicity `n`
and weighted digit-vector sum `u` — the index set of the multinomial theorem
for finite carry-free coefficients. Up to reordering, these are the tuples in the sum (3.4). -/
def powFiber (n : ℕ) (u : DigitSeries) : Set (DigitSeries →₀ ℕ) :=
  {φ | card φ = n ∧ total φ = u}

/-- Power fibers are finite: any member of the support of a `φ` in the fiber
is dominated pointwise by `u`, and there are finitely many such digit vectors,
each carrying multiplicity at most `n`. -/
theorem powFiber_finite (n : ℕ) (u : DigitSeries) : (powFiber n u).Finite := by
  classical
  have hB : {d : DigitSeries | ∀ i, d i ≤ u i}.Finite := finite_setOf_apply_le u
  refine (Set.finite_Iic (Finsupp.indicator hB.toFinset fun _ _ => n)).subset ?_
  rintro φ ⟨hcard, htotal⟩
  refine Set.mem_Iic.mpr (Finsupp.le_def.mpr fun d => ?_)
  by_cases hd : d ∈ φ.support
  · have hdB : d ∈ hB.toFinset := by
      rw [Set.Finite.mem_toFinset]
      intro i
      rw [← htotal]
      exact Multiplicity.apply_le_total φ hd i
    rw [Finsupp.indicator_of_mem hdB]
    calc
      φ d ≤ ∑ e ∈ φ.support, φ e :=
          Finset.single_le_sum (fun e _ => Nat.zero_le _) hd
      _ = card φ := (card_eq_sum φ).symm
      _ = n := hcard
  · rw [Finsupp.notMem_support_iff.mp hd]
    exact Nat.zero_le _

/-!
### Finite convolution of coefficient families

The coefficient at a proper vector `u` is a finite sum over `a + b = u`.
Both summands are proper because their digits are bounded by those of `u`.
Ordinary multivariate power series are used only to establish the multinomial
formula for these finite sums.
-/

/-- Coefficient families over `K`: all functions
from the set `ℙ` of proper digit vectors to `K`. -/
def DigitCoefficients (p : ℕ) [Fact (Nat.Prime p)] (K : Type*) : Type _ :=
  {d : DigitSeries // d.IsP p} → K

namespace DigitCoefficients

variable {p : ℕ} [Fact (Nat.Prime p)] {K : Type*} [CommRing K]

/-- Restriction of a power series in the digit positions to its coefficients
at proper exponents. -/
noncomputable def restrictMv (F : MvPowerSeries ℕ+ K) : DigitCoefficients p K :=
  fun u => MvPowerSeries.coeff u.1 F

@[simp] lemma restrictMv_apply (F : MvPowerSeries ℕ+ K)
    (u : {d : DigitSeries // d.IsP p}) :
    restrictMv F u = MvPowerSeries.coeff u.1 F := rfl

open Classical in
/-- Extension of a coefficient function on proper digit vectors by zero. -/
noncomputable def extendMv (A : DigitCoefficients p K) : MvPowerSeries ℕ+ K :=
  fun m => if h : DigitSeries.IsP m p then A ⟨m, h⟩ else 0

lemma extendMv_apply_of_isP (A : DigitCoefficients p K) {m : ℕ+ →₀ ℕ}
    (h : DigitSeries.IsP m p) : extendMv A m = A ⟨m, h⟩ :=
  dif_pos h

@[simp] lemma restrictMv_extendMv (A : DigitCoefficients p K) :
    restrictMv (extendMv A) = A :=
  funext fun u => dif_pos u.2

/-- The left part of a decomposition of a proper exponent is proper. -/
lemma isP_of_add_left {u : DigitSeries} (hu : u.IsP p) {a b : ℕ+ →₀ ℕ}
    (hab : a + b = u) : DigitSeries.IsP a p := by
  intro i
  have h : a i + b i = u i := DFunLike.congr_fun hab i
  exact lt_of_le_of_lt (h ▸ Nat.le_add_right (a i) (b i)) (hu i)

/-- The right part of a decomposition of a proper exponent is proper. -/
lemma isP_of_add_right {u : DigitSeries} (hu : u.IsP p) {a b : ℕ+ →₀ ℕ}
    (hab : a + b = u) : DigitSeries.IsP b p :=
  isP_of_add_left hu (by rw [add_comm]; exact hab)

/-- The coefficients of a product at proper exponents depend only on the
coefficients of the factors at proper exponents. -/
lemma restrictMv_mul_restrictMv (F G : MvPowerSeries ℕ+ K) :
    restrictMv (p := p)
        (extendMv (restrictMv (p := p) F) * extendMv (restrictMv (p := p) G)) =
      restrictMv (F * G) := by
  funext u
  rw [restrictMv_apply, restrictMv_apply, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hab := Finset.mem_antidiagonal.mp hx
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply,
    MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply,
    extendMv_apply_of_isP _ (isP_of_add_left u.2 hab),
    extendMv_apply_of_isP _ (isP_of_add_right u.2 hab),
    restrictMv_apply, restrictMv_apply]
  rfl

/-- The coefficient family of the empty tuple. -/
noncomputable def unit : DigitCoefficients p K := restrictMv 1

/-- Binary carry-free convolution, a finite sum at each proper digit vector. -/
noncomputable def convolve (A B : DigitCoefficients p K) : DigitCoefficients p K :=
  fun u => ∑ x ∈ Finset.antidiagonal u.1, extendMv A x.1 * extendMv B x.2

lemma convolve_eq_restrict (A B : DigitCoefficients p K) :
    convolve A B = restrictMv (extendMv A * extendMv B) := by
  funext u
  rw [restrictMv_apply, MvPowerSeries.coeff_mul]
  rfl

lemma convolve_restrict (F G : MvPowerSeries ℕ+ K) :
    convolve (restrictMv (p := p) F) (restrictMv G) = restrictMv (F * G) := by
  rw [convolve_eq_restrict, restrictMv_mul_restrictMv]

/-- Iterating finite convolution computes the sum over ordered tuples. At a proper vector
`u`, the `n`-th power is the sum `S_n(u)` of (3.4). -/
noncomputable def power (A : DigitCoefficients p K) : ℕ → DigitCoefficients p K
  | 0 => unit
  | n + 1 => convolve (power A n) A

lemma power_restrict (F : MvPowerSeries ℕ+ K) (n : ℕ) :
    power (restrictMv (p := p) F) n = restrictMv (F ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power, ih, convolve_restrict, pow_succ]

lemma convolve_apply (A B : DigitCoefficients p K) (u : {d : DigitSeries // d.IsP p}) :
    convolve A B u = ∑ x ∈ Finset.antidiagonal u.1,
      extendMv A x.1 * extendMv B x.2 := rfl

open Classical in
lemma unit_apply (u : {d : DigitSeries // d.IsP p}) :
    (unit : DigitCoefficients p K) u = if u.1 = 0 then 1 else 0 := by
  rw [unit, restrictMv_apply, MvPowerSeries.coeff_one]

section Multinomial

open Multiplicity

/-- Coefficients of a product at exponents `≤ m` depend only on the factors'
coefficients at exponents `≤ m`. -/
private lemma coeff_mul_congr {m : ℕ+ →₀ ℕ} {F F' G G' : MvPowerSeries ℕ+ K}
    (hF : ∀ x ≤ m, MvPowerSeries.coeff x F = MvPowerSeries.coeff x G)
    (hF' : ∀ x ≤ m, MvPowerSeries.coeff x F' = MvPowerSeries.coeff x G') :
    ∀ x ≤ m, MvPowerSeries.coeff x (F * F') = MvPowerSeries.coeff x (G * G') := by
  intro x hx
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ab hab => ?_
  have h := Finset.mem_antidiagonal.mp hab
  rw [hF ab.1 (((self_le_add_right ab.1 ab.2).trans_eq h).trans hx),
    hF' ab.2 (((self_le_add_left ab.2 ab.1).trans_eq h).trans hx)]

/-- Coefficients of a power at exponents `≤ m` depend only on the base's
coefficients at exponents `≤ m`. -/
private lemma coeff_pow_congr {m : ℕ+ →₀ ℕ} {F G : MvPowerSeries ℕ+ K}
    (h : ∀ x ≤ m, MvPowerSeries.coeff x F = MvPowerSeries.coeff x G) (n : ℕ) :
    ∀ x ≤ m, MvPowerSeries.coeff x (F ^ n) = MvPowerSeries.coeff x (G ^ n) := by
  induction n with
  | zero => intro x _; rw [pow_zero, pow_zero]
  | succ n ih =>
    intro x hx
    rw [pow_succ, pow_succ]
    exact coeff_mul_congr ih h x hx

/-- Below `m`, a power series agrees with its truncation to exponents `≤ m`. -/
private lemma coeff_truncation (F : MvPowerSeries ℕ+ K) (m : ℕ+ →₀ ℕ) :
    ∀ x ≤ m, MvPowerSeries.coeff x F =
      MvPowerSeries.coeff x
        (∑ y ∈ Finset.Iic m, MvPowerSeries.monomial y (MvPowerSeries.coeff y F)) := by
  intro x hx
  rw [map_sum, Finset.sum_congr rfl fun y _ => MvPowerSeries.coeff_monomial x y _,
    Finset.sum_ite_eq (Finset.Iic m) x, if_pos (Finset.mem_Iic.mpr hx)]

open Classical in
/-- The multiplicity function on digit vectors associated to an exponent-indexed
multiplicity function `k` supported on `Finset.Iic m`. -/
private noncomputable def toFiber (m : DigitSeries) (k : DigitSeries → ℕ) : DigitSeries →₀ ℕ :=
  Finsupp.onFinset (Finset.Iic m)
    (fun d => if d ∈ Finset.Iic m then k d else 0)
    (fun d hd => by
      by_contra h
      simp [h] at hd)

open Classical in
private lemma toFiber_apply (m : ℕ+ →₀ ℕ) (k : (ℕ+ →₀ ℕ) → ℕ) (d : DigitSeries) :
    toFiber m k d = if d ∈ Finset.Iic m then k d else 0 := rfl

open Classical in
private lemma toFiber_support_subset (m : ℕ+ →₀ ℕ) (k : (ℕ+ →₀ ℕ) → ℕ) :
    (toFiber m k).support ⊆ Finset.Iic m :=
  Finsupp.support_onFinset_subset

open Classical in
/-- Sums over the finite multiplicity function are sums over the bounded exponent set. -/
private lemma toFiber_sum {M : Type*} [AddCommMonoid M] (m : DigitSeries)
    (k : DigitSeries → ℕ) (g : DigitSeries → ℕ → M) (hg : ∀ d, g d 0 = 0) :
    (toFiber m k).sum g = ∑ y ∈ Finset.Iic m, g y (k y) := by
  rw [Finsupp.sum_of_support_subset _ (toFiber_support_subset m k) g fun d _ => hg d]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [toFiber_apply, if_pos hy]

open Classical in
/-- **Finite multinomial formula**: for a coefficient family `H` and a proper `u`,
`power H n u` is the finite sum over multiplicity
functions `φ` with `|φ| = n` and `Σ(φ) = u`, of the multinomial coefficient
`n! / ∏_d φd!` times `∏_d H_d^{φd}`, where `H_d = extendMv H d`
is the coefficient of `H` at `d`. This groups the sum (3.4) by multiplicities. -/
theorem power_apply (H : DigitCoefficients p K) (n : ℕ) (u : {d : DigitSeries // d.IsP p}) :
    power H n u = ∑ φ ∈ (powFiber_finite n u.1).toFinset,
      (Nat.multinomial φ.support φ : K) *
        ∏ d ∈ φ.support, extendMv H d ^ φ d := by
  classical
  set m : ℕ+ →₀ ℕ := u.1 with hm
  -- Step 1: transport to a coefficient of `(extendMv H) ^ n` in `MvPowerSeries`.
  have h1 : power H n u = MvPowerSeries.coeff m ((extendMv H) ^ n) := by
    conv_lhs => rw [← restrictMv_extendMv H, power_restrict]
    rfl
  -- Step 2: truncate the base to exponents `≤ m`.
  have h2 : MvPowerSeries.coeff m ((extendMv H) ^ n) =
      MvPowerSeries.coeff m
        ((∑ y ∈ Finset.Iic m, MvPowerSeries.monomial y (extendMv H y)) ^ n) := by
    refine coeff_pow_congr (fun x hx => ?_) n m le_rfl
    have := coeff_truncation (extendMv H) m x hx
    rwa [Finset.sum_congr rfl fun y _ => by rw [MvPowerSeries.coeff_apply]] at this
  -- Step 3: expand the truncated power via the multinomial theorem.
  have h3 : MvPowerSeries.coeff m
        ((∑ y ∈ Finset.Iic m, MvPowerSeries.monomial y (extendMv H y)) ^ n) =
      ∑ k ∈ Finset.piAntidiag (Finset.Iic m) n,
        if m = ∑ y ∈ Finset.Iic m, k y • y then
          (Nat.multinomial (Finset.Iic m) k : K) * ∏ y ∈ Finset.Iic m, extendMv H y ^ k y
        else 0 := by
    rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_congr rfl fun y _ => MvPowerSeries.monomial_pow y (extendMv H y) (k y),
      MvPowerSeries.prod_monomial, ← nsmul_eq_mul, map_nsmul,
      MvPowerSeries.coeff_monomial, nsmul_eq_mul, mul_ite, mul_zero]
  -- Step 4: reindex the surviving terms by the power fiber.
  have hsupp_mem : ∀ φ : DigitSeries →₀ ℕ, total φ = u.1 →
      ∀ d ∈ φ.support, d ∈ Finset.Iic m := by
    intro φ hφ d hd
    rw [Finset.mem_Iic, hm]
    refine Finsupp.le_def.mpr fun i => ?_
    have h := Multiplicity.apply_le_total φ hd i
    rw [hφ] at h
    exact h
  rw [h1, h2, h3, ← Finset.sum_filter]
  refine Finset.sum_nbij' (i := fun k => toFiber m k)
    (j := fun φ y => φ y) ?_ ?_ ?_ ?_ ?_
  · -- `toFiber` lands in the power fiber.
    intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hsum, hksupp⟩, hcond⟩ := hk
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · exact (toFiber_sum m k (fun _ v => v) fun _ => rfl).trans hsum
    · exact (toFiber_sum m k (fun d v => v • d) fun d => zero_nsmul d).trans
        (hcond.symm.trans hm)
  · -- restriction to the exponent set lands in the multinomial index set.
    intro φ hφ
    rw [Set.Finite.mem_toFinset] at hφ
    obtain ⟨hcard, htotal⟩ := hφ
    have hφsupp := hsupp_mem φ htotal
    have hsub : φ.support ⊆ Finset.Iic m := hφsupp
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (Finsupp.sum_of_support_subset φ hsub (fun _ v => v) fun _ _ => rfl).symm.trans hcard
    · exact fun y hy => hφsupp y (Finsupp.mem_support_iff.mpr hy)
    · exact hm.trans (htotal.symm.trans
        (Finsupp.sum_of_support_subset φ hsub (fun d v => v • d) fun d _ => zero_nsmul d))
  · -- left inverse.
    intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    funext y
    rw [toFiber_apply]
    by_cases hy : y ∈ Finset.Iic m
    · rw [if_pos hy]
    · rw [if_neg hy]
      exact (not_ne_iff.mp (mt (hk.1.2 y) hy)).symm
  · -- right inverse.
    intro φ hφ
    rw [Set.Finite.mem_toFinset] at hφ
    have hφsupp := hsupp_mem φ hφ.2
    ext d
    rw [toFiber_apply]
    by_cases hd : d ∈ Finset.Iic m
    · rw [if_pos hd]
    · rw [if_neg hd]
      exact (Finsupp.notMem_support_iff.mp fun hmem => hd (hφsupp d hmem)).symm
  · -- the summands match.
    intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    have happly : ∀ y ∈ Finset.Iic m, toFiber m k y = k y := fun y hy => by
      rw [toFiber_apply, if_pos hy]
    congr 1
    · -- the multinomial coefficients agree.
      have hmult : Nat.multinomial (toFiber m k).support ⇑(toFiber m k) =
          Nat.multinomial (Finset.Iic m) k := by
        calc
          Nat.multinomial (toFiber m k).support ⇑(toFiber m k)
            = Nat.multinomial (Finset.Iic m) ⇑(toFiber m k) :=
              Nat.multinomial_congr_of_sdiff (toFiber_support_subset m k)
                (fun d hd => Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hd).2)
                (fun d _ => rfl)
          _ = Nat.multinomial (Finset.Iic m) k :=
              Nat.multinomial_congr fun y hy => happly y hy
      rw [hmult]
    · -- the coefficient products agree.
      have hprod : ∏ d ∈ (toFiber m k).support, extendMv H d ^ toFiber m k d
          = ∏ d ∈ Finset.Iic m,
              extendMv H d ^ toFiber m k d :=
        Finset.prod_subset (toFiber_support_subset m k) fun d _ hd => by
          rw [Finsupp.notMem_support_iff.mp hd, pow_zero]
      rw [hprod]
      refine Finset.prod_congr rfl fun y hy => ?_
      rw [happly y hy]

end Multinomial

end DigitCoefficients

end PAdicOrderType
