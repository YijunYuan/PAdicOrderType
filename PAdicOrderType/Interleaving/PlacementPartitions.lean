/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.FullBlockConvolution
import PAdicOrderType.Interleaving.WordPartitions
import PAdicOrderType.Digits.BlockSupport

/-!
# Position partitions and full-block decompositions

An ordered partition of word positions induces a decomposition of the placed
digit vector in which each block belongs entirely to one component. This is the
correspondence between ordered partitions and tuples of digit vectors in the proof of
Lemma 3.14.
-/

namespace PAdicOrderType

/-- Summing the two sublists converts ordered position partitions into
full-component decompositions. -/
lemma splitSums_eq_unshuffles {ι : Type*} (xs : List (ι →₀ ℕ)) :
    splitSums xs = (unshuffles xs).map (fun uv => (uv.1.sum, uv.2.sum)) := by
  induction xs with
  | nil => simp [splitSums, unshuffles]
  | cons a xs ih =>
    simp only [splitSums, unshuffles, ih, Multiset.map_add, Multiset.map_map,
      Function.comp_def, List.sum_cons]

/-- Placing a list of indexed letters is the sum of its individual placements. -/
lemma placeList_projections_eq_sum {s : ℕ} (B : ℕ → Finset ℕ+)
    (z : List ((Fin s → ℕ) × ℕ)) :
    placeList B (z.map Prod.fst) (z.map Prod.snd) =
      (z.map (fun ei => placeAt (B ei.2) ei.1)).sum := by
  induction z with
  | nil => simp
  | cons a z ih => simp only [List.map_cons, placeList_cons_cons, List.sum_cons, ih]

/-- Full-block decompositions of a placement are ordered partitions of its
indexed letters. -/
lemma splitSums_placedLetters {s : ℕ} (B : ℕ → Finset ℕ+)
    (w : List (Fin s → ℕ)) (l : List ℕ) :
    splitSums (placedLetters B w l) =
      (unshuffles (w.zip l)).map (fun uv =>
        (placeList B (uv.1.map Prod.fst) (uv.1.map Prod.snd),
          placeList B (uv.2.map Prod.fst) (uv.2.map Prod.snd))) := by
  rw [splitSums_eq_unshuffles, placedLetters, unshuffles_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro uv _
  simp only [Function.comp_def, placeList_projections_eq_sum]

end PAdicOrderType
