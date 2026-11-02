/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Sets containing a finite set

This file complements the measurable space on `Set α` of
`Mathlib.MeasureTheory.MeasurableSpace.Constructions`: the sets containing a given finite set form
a measurable set.
-/

public section

variable {α : Type*}

lemma setOf_coe_finset_subset (t : Finset α) :
    {s : Set α | ↑t ⊆ s} = ⋂ i ∈ t, {s | i ∈ s} := by
  ext
  simp [Set.subset_def]

lemma measurableSet_setOf_coe_finset_subset (t : Finset α) :
    MeasurableSet {s : Set α | ↑t ⊆ s} := by
  rw [setOf_coe_finset_subset]
  exact t.measurableSet_biInter fun i _ ↦ measurableSet_mem i
