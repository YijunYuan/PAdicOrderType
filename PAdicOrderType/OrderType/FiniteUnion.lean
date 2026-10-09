/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Digits.WordGapGeometry

/-!
# Order type of a finite union

A finite union of well-ordered subsets of `ℚ` of order type `< ω ^ r` has order
type `< ω ^ r`. The proof of Lemma 3.6 cites this fact from Altman, *Internal structure of
addition chains: well-ordering*, Proposition 5.3(1).

The proof avoids natural sums of ordinals: for `x` in the union, the ordinals
`ρ_i x = typeLT (P i ∩ Iio x) < ω ^ r` are encoded by their Cantor normal forms
as elements of `Lex (Fin r → ℕ)` (via `PAdicOrderType.typeLT_lex_pi_fin`), the
pointwise sum `ψ x = ∑ i, cnf (ρ_i x)` is strictly monotone in `x` (lexicographic
order is compatible with addition, and `ρ_i` strictly increases at points of
`P i`), and `ψ` takes values below a fixed element of `Lex (Fin r → ℕ)`, so the
union has order type below `ω ^ r`.
-/

namespace PAdicOrderType

open Ordinal

universe u

/-! ### Well-founded subsets and cut order types -/

/-- A subset of a set that is well-founded under `<` is well-founded under `<`. -/
theorem wellFoundedLT_of_subset {α : Type*} [Preorder α] {s t : Set α} [WellFoundedLT ↥t]
    (h : s ⊆ t) : WellFoundedLT ↥s :=
  ⟨InvImage.wf (Set.inclusion h) wellFounded_lt⟩

/-- Order types of well-founded subsets are monotone under inclusion. -/
theorem typeLT_le_of_subset {α : Type u} [LinearOrder α] {s t : Set α}
    [WellFoundedLT ↥s] [WellFoundedLT ↥t] (h : s ⊆ t) : typeLT ↥s ≤ typeLT ↥t :=
  Ordinal.typeLT_set_le_of_strictMono (Set.inclusion h) fun _ _ hab => hab

/-- The order type of the part of a well-founded set `s` lying strictly below `x`. -/
noncomputable def cutType {α : Type u} [LinearOrder α] (s : Set α) [WellFoundedLT ↥s] (x : α) :
    Ordinal.{u} :=
  haveI := wellFoundedLT_of_subset (s := s ∩ Set.Iio x) Set.inter_subset_left
  typeLT ↥(s ∩ Set.Iio x)

section cutType

variable {α : Type u} [LinearOrder α] (s : Set α) [WellFoundedLT ↥s]

/-- The cut order type is bounded by the order type of the whole set. -/
theorem cutType_le_typeLT (x : α) : cutType s x ≤ typeLT ↥s :=
  haveI := wellFoundedLT_of_subset (s := s ∩ Set.Iio x) Set.inter_subset_left
  typeLT_le_of_subset Set.inter_subset_left

/-- The cut order type is monotone in the cut point. -/
theorem cutType_mono {x y : α} (hxy : x ≤ y) : cutType s x ≤ cutType s y :=
  haveI := wellFoundedLT_of_subset (s := s ∩ Set.Iio x) Set.inter_subset_left
  haveI := wellFoundedLT_of_subset (s := s ∩ Set.Iio y) Set.inter_subset_left
  typeLT_le_of_subset (Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hxy))

/-- Cutting at an element of `s` gives an order type strictly below that of `s`. -/
theorem cutType_lt_typeLT {x : α} (hx : x ∈ s) : cutType s x < typeLT ↥s :=
  haveI := wellFoundedLT_of_subset (s := s ∩ Set.Iio x) Set.inter_subset_left
  Ordinal.typeLT_inter_Iio_lt hx

/-- The cut order type strictly increases when moving past an element of `s`. -/
theorem cutType_lt_cutType {x y : α} (hx : x ∈ s) (hxy : x < y) :
    cutType s x < cutType s y := by
  have := wellFoundedLT_of_subset (s := s ∩ Set.Iio x) Set.inter_subset_left
  have := wellFoundedLT_of_subset (s := s ∩ Set.Iio y) Set.inter_subset_left
  have := wellFoundedLT_of_subset (s := (s ∩ Set.Iio y) ∩ Set.Iio x) Set.inter_subset_left
  have h : (s ∩ Set.Iio y) ∩ Set.Iio x = s ∩ Set.Iio x := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iio]
    constructor
    · rintro ⟨⟨hz, -⟩, hzx⟩
      exact ⟨hz, hzx⟩
    · rintro ⟨hz, hzx⟩
      exact ⟨⟨hz, hzx.trans hxy⟩, hzx⟩
  calc
    cutType s x = typeLT ↥((s ∩ Set.Iio y) ∩ Set.Iio x) := (Ordinal.typeLT_set_congr h).symm
    _ < typeLT ↥(s ∩ Set.Iio y) := Ordinal.typeLT_inter_Iio_lt ⟨hx, hxy⟩
    _ = cutType s y := rfl

end cutType

/-! ### Ordinals below `ω ^ r` as elements of lexicographic `ℕ ^ r` -/

/-- An ordinal `o < ω ^ r` encoded as the `o`-th element of lexicographic `ℕ ^ r`
(its Cantor normal form), via `PAdicOrderType.typeLT_lex_pi_fin`. -/
noncomputable def lexOfLt (r : ℕ) (o : Ordinal) (ho : o < omega0 ^ r) : Lex (Fin r → ℕ) :=
  enum (α := Lex (Fin r → ℕ)) (· < ·) ⟨o, by rw [typeLT_lex_pi_fin]; exact ho⟩

/-- `lexOfLt` reflects the strict order. -/
theorem lexOfLt_lt_lexOfLt {r : ℕ} {o₁ o₂ : Ordinal} (h₁ : o₁ < omega0 ^ r)
    (h₂ : o₂ < omega0 ^ r) : lexOfLt r o₁ h₁ < lexOfLt r o₂ h₂ ↔ o₁ < o₂ :=
  enum_lt_enum

/-- `lexOfLt` reflects the order. -/
theorem lexOfLt_le_lexOfLt {r : ℕ} {o₁ o₂ : Ordinal} (h₁ : o₁ < omega0 ^ r)
    (h₂ : o₂ < omega0 ^ r) : lexOfLt r o₁ h₁ ≤ lexOfLt r o₂ h₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.mpr (lexOfLt_lt_lexOfLt h₂ h₁)

/-- **Order type of a finite union**: if a
well-ordered set `U ⊆ ℚ` is the union of finitely many subsets `P i`, each of
order type `< ω ^ r`, then `typeLT U < ω ^ r`. This is the finite-union step in the proof
of Lemma 3.6. -/
theorem typeLT_lt_omega0_pow_of_iUnion {ι : Type*} [Finite ι] {P : ι → Set ℚ}
    [∀ i, WellFoundedLT ↥(P i)] {U : Set ℚ} [WellFoundedLT ↥U] (hU : U = ⋃ i, P i)
    {r : ℕ} (hP : ∀ i, typeLT ↥(P i) < omega0 ^ r) :
    typeLT ↥U < omega0 ^ r := by
  cases nonempty_fintype ι
  have hcut : ∀ i x, cutType (P i) x < omega0 ^ r := fun i x =>
    (cutType_le_typeLT _ _).trans_lt (hP i)
  -- the pointwise sum of the Cantor normal forms of the cut ranks
  let ψ : ℚ → Lex (Fin r → ℕ) := fun x => ∑ i, lexOfLt r (cutType (P i) x) (hcut i x)
  let M : Lex (Fin r → ℕ) := ∑ i, lexOfLt r (typeLT ↥(P i)) (hP i)
  have hψM : ∀ x ∈ U, ψ x < M := by
    intro x hx
    rw [hU, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    exact Finset.sum_lt_sum (fun i _ => (lexOfLt_le_lexOfLt _ _).mpr (cutType_le_typeLT _ _))
      ⟨j, Finset.mem_univ _, (lexOfLt_lt_lexOfLt _ _).mpr (cutType_lt_typeLT _ hj)⟩
  have hψ : ∀ x ∈ U, ∀ y, x < y → ψ x < ψ y := by
    intro x hx y hxy
    rw [hU, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    exact Finset.sum_lt_sum (fun i _ => (lexOfLt_le_lexOfLt _ _).mpr (cutType_mono _ hxy.le))
      ⟨j, Finset.mem_univ _, (lexOfLt_lt_lexOfLt _ _).mpr (cutType_lt_cutType _ hj hxy)⟩
  have key := Ordinal.typeLT_set_le_of_rank (s := U)
    (β := typein (α := Lex (Fin r → ℕ)) (· < ·) M)
    (fun x => typein (α := Lex (Fin r → ℕ)) (· < ·) (ψ x.1))
    (fun x y hxy => (typein_lt_typein _).mpr (hψ x.1 x.2 y.1 hxy))
    (fun x => (typein_lt_typein _).mpr (hψM x.1 x.2))
  refine key.trans_lt ?_
  rw [← typeLT_lex_pi_fin r]
  exact typein_lt_type _ _

end PAdicOrderType
