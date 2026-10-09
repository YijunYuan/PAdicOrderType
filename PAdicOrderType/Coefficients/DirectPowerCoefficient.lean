/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import PAdicOrderType.Interleaving.PlacementPartitions
import PAdicOrderType.Interleaving.InterleavingEstimate

/-!
# The maximal-block coefficient as a finite interleaving sum

At the maximal possible block count, every factor contributes entire blocks.
The carry-free coefficient is therefore the finite sum over ordered partitions
of the output positions, exactly the corresponding interleaving coefficient. This is the
interleaving identity (3.11) of Lemma 3.14.
-/

namespace PAdicOrderType

lemma placeList_covered {s : ℕ} (B : ℕ → Finset ℕ+)
    (w : List (Fin s → ℕ)) (l : List ℕ) :
    ∀ pos, placeList B w l pos ≠ 0 → ∃ j, pos ∈ B j := by
  classical
  intro pos hne
  by_contra h
  apply hne
  exact placeList_apply_eq_zero B w l (fun j _ hj => h ⟨j, hj⟩)

/-- **Interleaving identity** (Lemma 3.14): the top coefficient of a carry-free power is the
finite ordered-partition coefficient on words of the maximal length. With `A` the coefficients
`A_d` and `G w = A_w`, this is identity (3.11) for `S_n(u_z)`. -/
theorem power_coeff_placeList_eq_interleavingPower
    {p : ℕ} [Fact (Nat.Prime p)] {K : Type*} [Field K]
    {s : ℕ} {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    (hcard : ∀ j, (B j).card = s)
    (A : DigitCoefficients p K) (G : List (Fin s → ℕ) →₀ K) {r : ℕ}
    (hA : ∀ v : {d : DigitSeries // d.IsP p}, A v ≠ 0 →
      (∀ pos, v.1 pos ≠ 0 → ∃ j, pos ∈ B j) →
      (hitBlocks B (v.1)).card ≤ r)
    (hG : ∀ w ∈ G.support, w.length = r)
    (hbase : ∀ (w : List (Fin s → ℕ)) (l : List ℕ), w.length = r →
      (∀ e ∈ w, e ≠ 0) → (∀ e ∈ w, ∀ t, e t < p) →
      l.Pairwise (· < ·) → l.length = w.length →
      DigitCoefficients.extendMv A (placeList B w l) = G w)
    (n : ℕ) (w : List (Fin s → ℕ)) (l : List ℕ)
    (hlen : w.length = n*r) (hwnz : ∀ e ∈ w, e ≠ 0)
    (hwlt : ∀ e ∈ w, ∀ t, e t < p)
    (hl : l.Pairwise (· < ·)) (hll : l.length = w.length) :
    DigitCoefficients.extendMv (DigitCoefficients.power A n) (placeList B w l) =
      interleavingPower K G n w := by
  classical
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hproper (w : List (Fin s → ℕ)) (l : List ℕ)
      (hw : ∀ e ∈ w, ∀ t, e t < p) (hl : l.Pairwise (· < ·)) :
      DigitSeries.IsP ((placeList B w l)) p :=
    placeList_lt hdisj hp w l hw hl
  have hcount (w : List (Fin s → ℕ)) (l : List ℕ)
      (hnz : ∀ e ∈ w, e ≠ 0) (hl : l.Pairwise (· < ·))
      (hlen : l.length = w.length) :
      (hitBlocks B (placeList B w l)).card = w.length := by
    rw [hitBlocks_placeList hdisj hcard w l hnz hlen,
      List.toFinset_card_of_nodup (hl.imp ne_of_lt), hlen]
  have hbound (n : ℕ) (w : List (Fin s → ℕ)) (l : List ℕ)
      (hnz : ∀ e ∈ w, e ≠ 0) (hvalid : ∀ e ∈ w, ∀ t, e t < p)
      (hls : l.Pairwise (· < ·)) (hll : l.length = w.length)
      (hne : DigitCoefficients.extendMv (DigitCoefficients.power A n)
        (placeList B w l) ≠ 0) : w.length ≤ n*r := by
    let v : {d : DigitSeries // d.IsP p} :=
      ⟨(placeList B w l), hproper w l hvalid hls⟩
    rw [DigitCoefficients.extendMv_apply_of_isP _ v.2] at hne
    have hc := hitBlocks_power_le_supported hdisj A hA n v (placeList_covered B w l) hne
    simpa only [v, hcount w l hnz hls hll] using hc
  induction n generalizing w l with
  | zero =>
      have hw : w = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst w
      have hp0 : DigitSeries.IsP (0 : DigitSeries) p := fun _ => hp
      simp [placeList_nil, DigitCoefficients.power, DigitCoefficients.extendMv,
        DigitCoefficients.unit_apply, interleavingPower, hp0]
  | succ n ih =>
      let u : {d : DigitSeries // d.IsP p} :=
        ⟨(placeList B w l), hproper w l hwlt hl⟩
      have hconv := convolve_eq_splitSums (DigitCoefficients.power A n) A u
        (placedLetters B w l) (by
          simpa only [u] using (placedLetters_sum B w l))
        (placedLetters_ne_zero hcard w l hwnz)
        (placedLetters_pairwise_disjoint hdisj w l hl) (by
          intro x y hxy hne
          have hxP := DigitCoefficients.isP_of_add_left u.2 hxy
          have hyP := DigitCoefficients.isP_of_add_right u.2 hxy
          have hxne := left_ne_zero_of_mul hne
          have hyne := right_ne_zero_of_mul hne
          rw [DigitCoefficients.extendMv_apply_of_isP _ hxP] at hxne
          rw [DigitCoefficients.extendMv_apply_of_isP _ hyP] at hyne
          have hxle : x ≤ placeList B w l := by
            change x ≤ u.1
            rw [← hxy]; exact le_self_add
          have hyle : y ≤ placeList B w l := by
            change y ≤ u.1
            rw [← hxy]; exact le_add_self
          have hxcover := covered_by_blocks_of_le hxle (placeList_covered B w l)
          have hycover := covered_by_blocks_of_le hyle (placeList_covered B w l)
          have hxbound := hitBlocks_power_le_supported hdisj A hA n
            ⟨x, hxP⟩ hxcover hxne
          have hybound := hA ⟨y, hyP⟩ hyne hycover
          have hxycount : (hitBlocks B (x+y)).card = n*r+r := by
            rw [hxy, hcount w l hwnz hl hll, hlen]
            ring
          exact whole_placed_letter hdisj
            (hitBlocks_disjoint_of_maximal hdisj hxbound hybound hxycount) w l)
      rw [DigitCoefficients.extendMv_apply_of_isP _ u.2]
      change DigitCoefficients.convolve (DigitCoefficients.power A n) A u = _
      rw [hconv, splitSums_placedLetters, Multiset.map_map, interleavingPower,
        interleavingProduct_eq_unshuffles]
      have hun : (unshuffles (w.zip l)).map (fun uv =>
          (uv.1.map Prod.fst, uv.2.map Prod.fst)) = unshuffles w := by
        rw [← unshuffles_map, List.map_fst_zip hll.symm.le]
      rw [← hun, Multiset.map_map]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro uv huv
      obtain ⟨hsub1, hsub2⟩ := unshuffles_sublists huv
      have hwsub1 : (uv.1.map Prod.fst).Sublist w := by
        simpa only [List.map_fst_zip hll.symm.le] using hsub1.map Prod.fst
      have hwsub2 : (uv.2.map Prod.fst).Sublist w := by
        simpa only [List.map_fst_zip hll.symm.le] using hsub2.map Prod.fst
      have hlsub1 : (uv.1.map Prod.snd).Sublist l := by
        simpa only [List.map_snd_zip hll.le] using hsub1.map Prod.snd
      have hlsub2 : (uv.2.map Prod.snd).Sublist l := by
        simpa only [List.map_snd_zip hll.le] using hsub2.map Prod.snd
      have hnz1 : ∀ e ∈ uv.1.map Prod.fst, e ≠ 0 := fun e he => hwnz e (hwsub1.subset he)
      have hnz2 : ∀ e ∈ uv.2.map Prod.fst, e ≠ 0 := fun e he => hwnz e (hwsub2.subset he)
      have hv1 : ∀ e ∈ uv.1.map Prod.fst, ∀ t, e t < p := fun e he => hwlt e (hwsub1.subset he)
      have hv2 : ∀ e ∈ uv.2.map Prod.fst, ∀ t, e t < p := fun e he => hwlt e (hwsub2.subset he)
      have hs1 : (uv.1.map Prod.snd).Pairwise (· < ·) := hl.sublist hlsub1
      have hs2 : (uv.2.map Prod.snd).Pairwise (· < ·) := hl.sublist hlsub2
      have hlen1 : (uv.1.map Prod.snd).length = (uv.1.map Prod.fst).length := by simp
      have hlen2 : (uv.2.map Prod.snd).length = (uv.2.map Prod.fst).length := by simp
      have hsumlen : (uv.1.map Prod.fst).length + (uv.2.map Prod.fst).length = (n+1)*r := by
        simpa only [List.length_map, List.length_zip, hll, min_self, hlen] using
          unshuffles_lengths huv
      dsimp only [Function.comp_def]
      by_cases hmatch : (uv.1.map Prod.fst).length = n*r ∧ (uv.2.map Prod.fst).length = r
      · rw [ih _ _ hmatch.1 hnz1 hv1 hs1 hlen1,
          hbase _ _ hmatch.2 hnz2 hv2 hs2 hlen2]
      · have hleft : DigitCoefficients.extendMv (DigitCoefficients.power A n)
              (placeList B (uv.1.map Prod.fst) (uv.1.map Prod.snd)) *
            DigitCoefficients.extendMv A
              (placeList B (uv.2.map Prod.fst) (uv.2.map Prod.snd)) = 0 := by
          by_contra hne
          have h1 := hbound n _ _ hnz1 hv1 hs1 hlen1 (left_ne_zero_of_mul hne)
          have h2 : (uv.2.map Prod.fst).length ≤ r := by
            have hp2 := hproper _ _ hv2 hs2
            have hn2 := right_ne_zero_of_mul hne
            rw [DigitCoefficients.extendMv_apply_of_isP _ hp2] at hn2
            have hb := hA ⟨(placeList B (uv.2.map Prod.fst)
              (uv.2.map Prod.snd)), hp2⟩ hn2 (placeList_covered B _ _)
            simpa only [hcount _ _ hnz2 hs2 hlen2] using hb
          apply hmatch
          rw [Nat.add_mul, Nat.one_mul] at hsumlen
          omega
        have hright : interleavingPower K G n (uv.1.map Prod.fst) * G (uv.2.map Prod.fst) = 0 := by
          by_contra hne
          apply hmatch
          exact ⟨length_eq_of_mem_support_pow hG n _
            (Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)),
            hG _ (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne))⟩
        rw [hleft, hright]

end PAdicOrderType
