/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.MainResults
import PAdicOrderType.ShadowMap

/-!
# Algebraic p-adic Hahn series

This entry point imports the formalization of the paper cited below: the support order-type
dichotomy, the strict p-adic Puiseux characterization, the bialgebraicity criterion, and the
shadow homeomorphism on completed algebraic closures.

## Main statements

* `PAdicOrderType.typeLT_support_le_omega0_or_eq_omega0_pow_omega0`: an algebraic p-adic
  Hahn series has support order type at most `ω` or exactly `ω ^ ω` (Theorem A).
* `PAdicOrderType.support_finite_of_isAlgebraic_of_isBounded`: an algebraic p-adic Hahn
  series with bounded support has finite support (Theorem B).
* `PAdicOrderType.typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range`: among algebraic
  series, support order type at most `ω` characterizes the strict Puiseux image (Theorem C).
* `PAdicOrderType.bialgebraic_tfae`: simultaneous algebraicity of a Hahn series and its shadow
  is equivalent to bounded exponent denominators and finite coefficient range (Theorem D).
* `PAdicOrderType.image_shadow_closure_algebraicClosure_eq_range_ofPadicComplex`: the shadow
  map identifies the completed characteristic-p algebraic closure with the p-adic complex field
  (Proposition 2.9).

## References

* S. Wang and Y. Yuan, *The order types of the supports of p-adic algebraic Hahn series*.
  Theorem, proposition, lemma, and definition numbers in this library refer to this paper.
-/
