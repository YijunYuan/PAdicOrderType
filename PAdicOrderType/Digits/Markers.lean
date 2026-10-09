/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.CarryFreeCoefficients
import PAdicOrderType.Digits.WordGapGeometry

/-!
# Marker geometry and the carry-free top block

`PAdicOrderType.MarkerData` packages the nested triples
`b j ⊆ i j ⊆ bt j`: pairwise disjoint *core
blocks* `b j` of a common cardinality `s`, the *detection intervals*
`i j = [min (b j), max (b j) + h]`, and pairwise disjoint *protective intervals*
`bt j ⊇ i j`. A digit series is *clustered* (`MarkerData.IsClustered r d`) if
its support is covered by at most `r` clusters, each of which lies inside the
protective interval of every detection interval it meets. In the proof of Lemma 3.11, the
core blocks are the blocks `B_j`, the detection and protective intervals play the roles of
`B_j^+` and `B_j^{++}`, and the clusters are the pieces.

The main result is the **carry-free top block** lemma
`PAdicOrderType.MarkerData.carry_free`, the first assertion of Lemma 3.11:
for `n, r ≥ 1` and detection margin `h` with `n ≤ p ^ h`, if `u` is proper,
nonzero on each of `n * r` selected core blocks and zero
elsewhere, and `d₁, …, d_m` (`m ≤ n`) are proper clustered digit series with
`‖d₁‖ + ⋯ + ‖d_m‖ - ‖u‖ ∈ ℤ`, then `m = n` and `d₁ + ⋯ + d_m = u` (no carry
occurs). This is the rigid condition of Definition 3.3.
-/

namespace PAdicOrderType

/-! ### Auxiliary facts on digit series -/

/-- Membership in `DigitSeries.indices n`: the positions `1, …, n`. -/
lemma mem_indices_iff (n : ℕ) (i : ℕ+) : i ∈ DigitSeries.indices n ↔ (i : ℕ) ≤ n := by
  constructor
  · intro hi
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < n ∧ Nat.succPNat k = i := by
      simpa [DigitSeries.indices, eq_comm] using hi
    simp only [Nat.succPNat_coe]
    omega
  · intro hi
    have := i.pos
    rw [← PNat.succPNat_natPred i, DigitSeries.mem_indices]
    simp only [PNat.natPred]
    omega

/-- Taking `h`-tails commutes with finite sums of digit series. -/
lemma tailh_sum {m : ℕ} (d : Fin m → DigitSeries) (h : ℕ) :
    tailh (∑ i, d i) h = ∑ i, tailh (d i) h := by
  ext k
  simp only [tailh_apply, Finsupp.finsetSum_apply]

/-- **Gap detection**: let `z = d₁ + ⋯ + d_m` be a sum of `m ≤ n ≤ p ^ H` proper digit
series and `u` a proper digit series. If `z` vanishes on the window
`[b, b + H]` while `u b ≠ 0` and `u` vanishes on `(b, b + H]`, then
`‖z‖ - ‖u‖` is not an integer. (The carry recursion is
`c_{b+H+1} = p^H c_{b+1}` forcing `c_{b+1} = 0` and then `0 = u_b + p c_b`.) This is the
claim on the blocks `B^+` in the proof of Lemma 3.11. -/
lemma not_isInt_of_gap {p : ℕ} [Fact (Nat.Prime p)] {m n H : ℕ} (hmn : m ≤ n)
    (hH : n ≤ p ^ H) {d : Fin m → DigitSeries} (hd : ∀ i, DigitSeries.IsP (d i) p) {u : DigitSeries}
    (hu : u.IsP p) {b : ℕ+} (hub : u b ≠ 0)
    (hz : ∀ k : ℕ+, (b : ℕ) ≤ k → (k : ℕ) ≤ b + H → (∑ i, d i) k = 0)
    (hu0 : ∀ k : ℕ+, (b : ℕ) < k → (k : ℕ) ≤ b + H → u k = 0)
    (hres : ((∑ i, d i).norm p - u.norm p).isInt = true) : False := by
  set z : DigitSeries := ∑ i, d i with hzdef
  have hp : Nat.Prime p := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set h : ℕ := (b : ℕ) + H with hh
  -- the integer `N = ‖z‖ - ‖u‖`
  set N : ℤ := (z.norm p - u.norm p).num with hN
  have hNq : z.norm p - u.norm p = N := Rat.eq_num_of_isInt hres
  -- tail identities
  have hzid := pow_mul_norm_eq_pih_add_norm_tailh p z h
  have huid := pow_mul_norm_eq_pih_add_norm_tailh p u h
  -- `π_h z` is divisible by `p ^ (H + 1)`
  have hpz : p ^ (H + 1) ∣ pih p z h := by
    unfold pih
    refine Finset.dvd_sum fun i hi => ?_
    rw [mem_indices_iff] at hi
    by_cases hib : (b : ℕ) ≤ i
    · rw [hz i hib hi, zero_mul]
      exact dvd_zero _
    · exact Dvd.dvd.mul_left (pow_dvd_pow p (by omega)) _
  obtain ⟨a, ha⟩ := hpz
  -- `π_h u = u_b p^H + p^(H+1) c`
  have hbmem : b ∈ DigitSeries.indices h := (mem_indices_iff h b).2 (by omega)
  have hpu : ∃ c, pih p u h = u b * p ^ H + p ^ (H + 1) * c := by
    unfold pih
    rw [← Finset.add_sum_erase _ _ hbmem]
    have hrest : p ^ (H + 1) ∣
        ∑ i ∈ (DigitSeries.indices h).erase b, u i * p ^ (h - (i : ℕ)) := by
      refine Finset.dvd_sum fun i hi => ?_
      rw [Finset.mem_erase, mem_indices_iff] at hi
      obtain ⟨hib, hih⟩ := hi
      rcases lt_or_gt_of_ne (fun heq : (i : ℕ) = b => hib (PNat.eq heq)) with hlt | hgt
      · exact Dvd.dvd.mul_left (pow_dvd_pow p (by omega)) _
      · rw [hu0 i hgt hih, zero_mul]
        exact dvd_zero _
    obtain ⟨c, hc⟩ := hrest
    refine ⟨c, ?_⟩
    rw [hc, show h - (b : ℕ) = H by omega]
  obtain ⟨c, hc⟩ := hpu
  -- the integer `Z = ‖tail_h z‖ - ‖tail_h u‖`
  set Z : ℤ := (p : ℤ) ^ h * N - (pih p z h : ℤ) + (pih p u h : ℤ) with hZ
  have hZq : (Z : ℚ) = (tailh z h).norm p - (tailh u h).norm p := by
    rw [hZ]
    push_cast
    have : (p : ℚ) ^ h * (z.norm p - u.norm p) = (p : ℚ) ^ h * N := by rw [hNq]
    linear_combination -this + hzid - huid
  -- bounds on the tail norms
  have htu := DigitSeries.norm_mem_Ico p _ (tailh_isP hu h)
  have htz_eq : tailh z h = ∑ i, tailh (d i) h := tailh_sum d h
  have htz0 : 0 ≤ (tailh z h).norm p := by
    rw [htz_eq, map_sum]
    exact Finset.sum_nonneg fun i _ => (DigitSeries.norm_mem_Ico p _ (tailh_isP (hd i) h)).1
  have htz1 : (tailh z h).norm p < (p : ℚ) ^ H := by
    rw [htz_eq, map_sum]
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact pow_pos (by exact_mod_cast hp.pos) H
    · calc
        ∑ i, (tailh (d i) h).norm p < ∑ _i : Fin m, (1 : ℚ) :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hm0⟩, Finset.mem_univ _⟩ fun i _ =>
              (DigitSeries.norm_mem_Ico p _ (tailh_isP (hd i) h)).2
        _ = m := by simp
        _ ≤ (p : ℚ) ^ H := by exact_mod_cast hmn.trans hH
  have hZ0 : 0 ≤ Z := by
    have h1 : (-1 : ℚ) < Z := by rw [hZq]; linarith [htu.2]
    have h2 : (-1 : ℤ) < Z := by exact_mod_cast h1
    omega
  have hZlt : Z < (p : ℤ) ^ H := by
    have h1 : (Z : ℚ) < (p : ℚ) ^ H := by rw [hZq]; linarith [htu.1]
    exact_mod_cast h1
  -- `Z` is a multiple of `p ^ H`, hence zero
  have hkey : Z = (p : ℤ) ^ H * ((p : ℤ) ^ (b : ℕ) * N - p * a + u b + p * c) := by
    rw [hZ, ha, hc, hh]
    push_cast
    ring
  have hZzero : Z = 0 :=
    Int.eq_zero_of_abs_lt_dvd ⟨_, hkey⟩ (by rwa [abs_of_nonneg hZ0])
  rw [hZzero] at hkey
  have hlin : (p : ℤ) ^ (b : ℕ) * N - p * a + u b + p * c = 0 :=
    (mul_eq_zero.mp hkey.symm).resolve_left (pow_ne_zero _ hp0)
  -- hence `p ∣ u b`, contradicting `0 < u b < p`
  obtain ⟨b', hb'⟩ : ∃ b', (b : ℕ) = b' + 1 := ⟨b.natPred, (PNat.natPred_add_one b).symm⟩
  have hpdvd : (p : ℤ) ∣ (u b : ℤ) := by
    refine ⟨a - c - (p : ℤ) ^ b' * N, ?_⟩
    rw [hb'] at hlin
    linear_combination hlin
  have hub0 : (u b : ℤ) = 0 :=
    Int.eq_zero_of_abs_lt_dvd hpdvd (by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hu b)
  exact hub (by exact_mod_cast hub0)

/-- **Marker data**: core blocks `B j` of
cardinality `s`, detection intervals `i j = [min (b j), max (b j) + h]`, and
pairwise disjoint protective intervals `bt j ⊇ i j`. These model the sets `B_j`, `B_j^+` and
`B_j^{++}` in the proof of Lemma 3.11. -/
structure MarkerData where
  /-- The common cardinality of the core blocks. -/
  s : ℕ
  /-- The core blocks. -/
  b : ℕ → Finset ℕ+
  /-- The detection intervals. -/
  i : ℕ → Finset ℕ+
  /-- The protective intervals. -/
  bt : ℕ → Finset ℕ+
  /-- The detection margin `h` (in the application, `p ^ h ≥ n`). -/
  h : ℕ
  /-- Every core block has cardinality `s`. -/
  card_b : ∀ j, (b j).card = s
  /-- Each core block lies in its detection interval. -/
  b_subset_i : ∀ j, b j ⊆ i j
  /-- Each detection interval lies in its protective interval. -/
  i_subset_bt : ∀ j, i j ⊆ bt j
  /-- `x ∈ i j ↔ min (b j) ≤ x ≤ max (b j) + h`. -/
  mem_i_iff : ∀ j (x : ℕ+),
    x ∈ i j ↔ (∃ y ∈ b j, y ≤ x) ∧ ∃ y ∈ b j, (x : ℕ) ≤ (y : ℕ) + h
  /-- Protective intervals with distinct indices are disjoint. -/
  bt_disjoint : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (bt i) (bt j)

namespace MarkerData

/-- A digit series `d` is *clustered with at most `r` clusters* relative to the
marker data: its support is covered by at most `r` finite sets (clusters), and
every cluster meeting a detection interval `I j` lies inside `Bt j`. The clusters are the
pieces in the proof of Lemma 3.11, obtained from Lemma 3.8. -/
def IsClustered (μ : MarkerData) (r : ℕ) (d : DigitSeries) : Prop :=
  ∃ cl : Finset (Finset ℕ+), cl.card ≤ r ∧ (∀ i : ℕ+, d i ≠ 0 → ∃ C ∈ cl, i ∈ C) ∧
    ∀ C ∈ cl, ∀ j, (C ∩ μ.i j).Nonempty → C ⊆ μ.bt j

/-- The core blocks are pairwise disjoint (they lie in the disjoint protective
intervals). -/
lemma b_disjoint (μ : MarkerData) ⦃i j : ℕ⦄ (hij : i ≠ j) : Disjoint (μ.b i) (μ.b j) :=
  (μ.bt_disjoint hij).mono ((μ.b_subset_i i).trans (μ.i_subset_bt i))
    ((μ.b_subset_i j).trans (μ.i_subset_bt j))

/-- **Top block degree is carry-free** (Lemma 3.11).
Let `J` be a set of `n * r` selected block indices (`n, r ≥ 1`, `n ≤ p ^ H`),
and let `u` be a proper digit series supported in `⋃ j ∈ J, B j` and nonzero on
each `B j` (`j ∈ J`). If `ds` is a multiset of at most `n` proper digit series,
each clustered with at most `r` clusters, and `∑ ‖d‖ - ‖u‖ ∈ ℤ`, then `ds` has
exactly `n` elements and `∑ d = u`. Thus `u` satisfies the rigid condition of
Definition 3.3. -/
theorem carry_free {p : ℕ} [Fact (Nat.Prime p)] (μ : MarkerData) {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) (hH : n ≤ p ^ μ.h) {J : Finset ℕ} (hJ : J.card = n * r)
    {u : DigitSeries} (hu : u.IsP p) (hu_supp : ∀ i : ℕ+, u i ≠ 0 → ∃ j ∈ J, i ∈ μ.b j)
    (hu_blocks : ∀ j ∈ J, ∃ i ∈ μ.b j, u i ≠ 0)
    {ds : Multiset DigitSeries} (hm : Multiset.card ds ≤ n)
    (hP : ∀ d ∈ ds, d.IsP p) (hcl : ∀ d ∈ ds, μ.IsClustered r d)
    (hres : ((ds.map (DigitSeries.norm p)).sum - u.norm p).isInt = true) :
    Multiset.card ds = n ∧ ds.sum = u := by
  classical
  obtain ⟨L, rfl⟩ : ∃ L : List DigitSeries, (L : Multiset DigitSeries) = ds :=
    ⟨ds.toList, Multiset.coe_toList ds⟩
  set d : Fin L.length → DigitSeries := fun i => L[(i : ℕ)] with hd
  have hsum : (L : Multiset DigitSeries).sum = ∑ i, d i := by
    rw [Multiset.sum_coe]
    exact (Fin.sum_univ_getElem L).symm
  rw [Multiset.coe_card] at hm
  rw [← map_multiset_sum, hsum] at hres
  rw [Multiset.coe_card, hsum]
  have hmem : ∀ i, d i ∈ (L : Multiset DigitSeries) := fun i =>
    Multiset.mem_coe.mpr (List.getElem_mem _)
  have hdP : ∀ i, DigitSeries.IsP (d i) p := fun i => hP _ (hmem i)
  choose cl hcl_card hcl_cov hcl_Bt using fun i => hcl (d i) (hmem i)
  set z : DigitSeries := ∑ i, d i with hz
  have hp : Nat.Prime p := Fact.out
  -- Step 1: every selected detection interval meets a labelled cluster
  have hmeet : ∀ j ∈ J, ∃ i : Fin L.length, ∃ C ∈ cl i, (C ∩ μ.i j).Nonempty := by
    intro j hj
    by_contra hno
    have hzI : ∀ k ∈ μ.i j, z k = 0 := by
      intro k hk
      rw [hz, Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_contra hne
      obtain ⟨C, hC, hkC⟩ := hcl_cov i k hne
      exact hno ⟨i, C, hC, k, Finset.mem_inter.mpr ⟨hkC, hk⟩⟩
    obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image ((μ.b j).filter fun i => u i ≠ 0)
      (fun i : ℕ+ => (i : ℕ)) (by
        obtain ⟨i, hi, hui⟩ := hu_blocks j hj
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, hui⟩⟩)
    rw [Finset.mem_filter] at hb
    have hI : ∀ k : ℕ+, (b : ℕ) ≤ k → (k : ℕ) ≤ b + μ.h → k ∈ μ.i j := fun k h1 h2 =>
      (μ.mem_i_iff j k).2 ⟨⟨b, hb.1, (PNat.coe_le_coe _ _).1 h1⟩, ⟨b, hb.1, h2⟩⟩
    refine not_isInt_of_gap hm hH hdP hu hb.2 ?_ ?_ hres
    · intro k h1 h2
      exact hzI k (hI k h1 h2)
    · intro k h1 h2
      by_contra hne
      obtain ⟨j', hj', hkB⟩ := hu_supp k hne
      have hkBt : k ∈ μ.bt j := μ.i_subset_bt j (hI k h1.le h2)
      have hkBt' : k ∈ μ.bt j' := (μ.b_subset_i j').trans (μ.i_subset_bt j') hkB
      by_cases hjj : j' = j
      · subst hjj
        have := hbmax k (Finset.mem_filter.mpr ⟨hkB, hne⟩)
        omega
      · exact Finset.disjoint_left.mp (μ.bt_disjoint hjj) hkBt' hkBt
  -- Step 2: counting labelled clusters
  set T : Finset (Σ _i : Fin L.length, Finset ℕ+) := Finset.univ.sigma cl with hT
  have hTcard : T.card ≤ L.length * r := by
    rw [hT, Finset.card_sigma]
    calc
      ∑ i, (cl i).card ≤ ∑ _i : Fin L.length, r := Finset.sum_le_sum fun i _ => hcl_card i
      _ = L.length * r := by simp
  have hJne : J.Nonempty := Finset.card_pos.mp (by rw [hJ]; positivity)
  obtain ⟨j₀, hj₀⟩ := hJne
  obtain ⟨i₀, -, -⟩ := hmeet j₀ hj₀
  have : Nonempty (Fin L.length) := ⟨i₀⟩
  choose! fi fC hfcl hfmeet using hmeet
  have hfT : ∀ j ∈ J, (⟨fi j, fC j⟩ : Σ _i : Fin L.length, Finset ℕ+) ∈ T := fun j hj => by
    rw [hT, Finset.mem_sigma]
    exact ⟨Finset.mem_univ _, hfcl j hj⟩
  have hfBt : ∀ j ∈ J, fC j ⊆ μ.bt j := fun j hj => hcl_Bt _ _ (hfcl j hj) j (hfmeet j hj)
  have hinj : Set.InjOn (fun j => (⟨fi j, fC j⟩ : Σ _i : Fin L.length, Finset ℕ+)) J := by
    intro j hj j' hj' hjj'
    by_contra hne
    obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp hjj'
    have hC : fC j = fC j' := eq_of_heq h2
    obtain ⟨k, hk⟩ := hfmeet j hj
    have hk1 : k ∈ μ.bt j := hfBt j hj (Finset.mem_inter.mp hk).1
    have hk2 : k ∈ μ.bt j' := hfBt j' hj' (hC ▸ (Finset.mem_inter.mp hk).1)
    exact Finset.disjoint_left.mp (μ.bt_disjoint hne) hk1 hk2
  have hcardJT : J.card ≤ T.card :=
    Finset.card_le_card_of_injOn _ (fun j hj => hfT j hj) hinj
  have hmn : L.length = n := by
    have : n * r ≤ L.length * r := hJ ▸ hcardJT.trans hTcard
    exact le_antisymm hm (Nat.le_of_mul_le_mul_right this hr)
  have hsurj : Set.SurjOn (fun j => (⟨fi j, fC j⟩ : Σ _i : Fin L.length, Finset ℕ+)) J T :=
    Finset.surjOn_of_injOn_of_card_le _ (fun j hj => hfT j hj) hinj
      (by rw [hJ, ← hmn]; exact hTcard)
  refine ⟨hmn, ?_⟩
  -- Step 3: at most one input is non-zero at each position, so no carry occurs
  have huniq : ∀ (k : ℕ+) (i i' : Fin L.length), d i k ≠ 0 → d i' k ≠ 0 → i = i' := by
    intro k i i' hi hi'
    obtain ⟨C, hC, hkC⟩ := hcl_cov i k hi
    obtain ⟨C', hC', hkC'⟩ := hcl_cov i' k hi'
    obtain ⟨j, hj, hfj⟩ := hsurj (Finset.mem_coe.mpr
      (show (⟨i, C⟩ : Σ _i : Fin L.length, Finset ℕ+) ∈ T by
        rw [hT, Finset.mem_sigma]; exact ⟨Finset.mem_univ _, hC⟩))
    obtain ⟨j', hj', hfj'⟩ := hsurj (Finset.mem_coe.mpr
      (show (⟨i', C'⟩ : Σ _i : Fin L.length, Finset ℕ+) ∈ T by
        rw [hT, Finset.mem_sigma]; exact ⟨Finset.mem_univ _, hC'⟩))
    have hjj' : j = j' := by
      by_contra hne
      obtain ⟨-, hC1⟩ := Sigma.mk.inj_iff.mp hfj
      obtain ⟨-, hC2⟩ := Sigma.mk.inj_iff.mp hfj'
      have hk1 : k ∈ μ.bt j := hfBt j hj (by rw [eq_of_heq hC1]; exact hkC)
      have hk2 : k ∈ μ.bt j' := hfBt j' hj' (by rw [eq_of_heq hC2]; exact hkC')
      exact Finset.disjoint_left.mp (μ.bt_disjoint hne) hk1 hk2
    subst hjj'
    exact (Sigma.mk.inj_iff.mp (hfj.symm.trans hfj')).1
  have hzP : z.IsP p := by
    intro k
    rw [hz, Finsupp.finsetSum_apply]
    by_cases hex : ∃ i, d i k ≠ 0
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i (fun i' _ hi' => by
          by_contra h
          exact hi' (huniq k i' i h hi)) (fun h => absurd (Finset.mem_univ i) h)]
      exact hdP i k
    · push Not at hex
      simp only [hex, Finset.sum_const_zero]
      exact hp.pos
  exact DigitSeries.eq_of_norm_sub_isInt hzP hu hres

end MarkerData

end PAdicOrderType
