/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Almost all subsets of a finite type

A property holds for almost all subsets of a family of finite types when the proportion of the
subsets with the property tends to `1`. This file shows that this follows from a bound
`ε * 2 ^ |α|` on the number of exceptional subsets, with `ε` tending to `0`. Green states
Theorems 7 and 9 in this form, and proves them through such bounds.

## Main statements

* `tendsto_card_filter_div_two_pow_of_card_filter_not_le`: the proportion of the subsets with a
  property tends to `1` when the number of exceptions is eventually at most `ε * 2 ^ |α|` with
  `ε → 0`.
-/

@[expose] public section

namespace CountingSetsWithSmallSumset

open Finset Filter Topology

/-- Let `α i` have `n i` elements. If eventually at most `ε i * 2 ^ n i` subsets of `α i` fail
`P i`, and `ε i` tends to `0`, then the proportion of the subsets of `α i` satisfying `P i` tends
to `1`. -/
lemma tendsto_card_filter_div_two_pow_of_card_filter_not_le {ι : Type*} {l : Filter ι}
    {α : ι → Type*} [∀ i, Fintype (α i)] {n : ι → ℕ} (hn : ∀ i, Fintype.card (α i) = n i)
    (P : ∀ i, Finset (α i) → Prop) [∀ i, DecidablePred (P i)] {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (h : ∀ᶠ i in l, (#{A | ¬P i A} : ℝ) ≤ ε i * 2 ^ n i) :
    Tendsto (fun i ↦ (#{A | P i A} : ℝ) / 2 ^ n i) l (𝓝 1) := by
  have hcompl (i : ι) : (#{A | P i A} : ℝ) = 2 ^ n i - #{A | ¬P i A} := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast (by simpa [hn] using card_filter_add_card_filter_not (s := univ) (P i))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hε.const_sub 1)
    tendsto_const_nhds ?_ ?_
  · filter_upwards [h] with i hi
    rw [hcompl, sub_div, div_self (by positivity)]
    gcongr
    rwa [div_le_iff₀ (by positivity)]
  · filter_upwards with i
    rw [div_le_one (by positivity)]
    exact_mod_cast (card_le_univ _).trans_eq (by simp [hn])

end CountingSetsWithSmallSumset
