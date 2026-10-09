/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Interleaving.WordPartitions
import Mathlib.Data.Fintype.EquivFin

/-!
# Restricting interleaving coefficients to an alphabet

An output using only letters in a smaller alphabet receives contributions only
from inputs using that alphabet. Restriction therefore commutes with finite
interleaving products and their powers. This justifies the reduction to the letters of a
witness word in the proof of Lemma 3.15.
-/

namespace PAdicOrderType

variable {A L K : Type*}

/-- Keep the coefficients of words written in the injected alphabet. -/
noncomputable def restrictAlphabet [Zero K] (e : A ↪ L) (G : List L →₀ K) : List A →₀ K :=
  G.comapDomain (List.map e) (List.map_injective_iff.mpr e.injective).injOn

/-- Partitioning the positions of an output commutes with mapping its letters. -/
lemma restrictAlphabet_interleavingProduct [DecidableEq A] [DecidableEq L] [Semiring K]
    (e : A ↪ L) (F G : List L →₀ K) :
    restrictAlphabet e (interleavingProduct K F G) =
      interleavingProduct K (restrictAlphabet e F) (restrictAlphabet e G) := by
  ext w
  simp only [restrictAlphabet, Finsupp.comapDomain_apply, interleavingProduct_eq_unshuffles,
    unshuffles_map, Multiset.map_map, Function.comp_def]

/-- Restricting the input alphabet leaves all coefficients on that alphabet unchanged. -/
theorem restrictAlphabet_interleavingPower [DecidableEq A] [DecidableEq L] [CommRing K]
    (e : A ↪ L) (G : List L →₀ K) (n : ℕ) :
    restrictAlphabet e (interleavingPower K G n) =
      interleavingPower K (restrictAlphabet e G) n := by
  induction n with
  | zero =>
      ext w
      simp [interleavingPower, restrictAlphabet, Finsupp.single_apply]
  | succ n ih => rw [interleavingPower, restrictAlphabet_interleavingProduct, ih,
      interleavingPower]

/-- A witness word uses at most as many letters as it has positions. In the proof of
Lemma 3.15, the letters of the witness word `w₀` form an alphabet with at most `r` letters. -/
theorem exists_finAlphabet (w : List L) :
    ∃ k : ℕ, k ≤ w.length ∧
      ∃ e : Fin k ↪ L, ∃ v : List (Fin k), v.map e = w := by
  classical
  let s := w.toFinset
  let e : Fin s.card ↪ L :=
    s.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ s))
  let v : List (Fin s.card) := w.attach.map fun a =>
    s.equivFin ⟨a.val, List.mem_toFinset.mpr a.property⟩
  refine ⟨s.card, List.toFinset_card_le w, e, v, ?_⟩
  simp only [v, List.map_map, Function.comp_def, e, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, Function.Embedding.coe_subtype, Equiv.symm_apply_apply]
  simpa only [id_eq, List.map_id] using (List.attach_map_val (l := w) (f := id))

end PAdicOrderType
