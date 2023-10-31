/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2022, Problem 2

Let ℝ+ be the set of positive real numbers.
Determine all functions f: ℝ+ → ℝ+ such that
for each x ∈ ℝ+, there is exactly one y ∈ ℝ+
satisfying

  x·f(y) + y·f(x) ≤ 2
-/

namespace Imo2022P2

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

determine solution_set : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

problem imo2022_p2 (f : ℝ+ → ℝ+) :
    f ∈ solution_set ↔
    ∀ x, ∃! y, x * f y + y * f x ≤ ⟨2, two_pos⟩ := by
  constructor
  · intro hf
    simp only [Set.mem_singleton_iff] at hf
    rw [hf] at *; clear hf
    intro x
    use x
    constructor
    · suffices h : (1:ℝ+) + 1 = ⟨2, two_pos⟩ by
        simp only [one_div, mul_right_inv, ge_iff_le]
        exact Eq.le h
      norm_num [Subtype.ext_iff]
    · intro y hxy
      change (x * (1 / y) + y * (1 / x)).val ≤ _  at hxy
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      simp only [Positive.coe_add, Positive.val_mul, one_div, Positive.coe_inv] at hxy
      rw [Subtype.mk_eq_mk]
      have hxyp : 0 < y * x := Real.mul_pos hy hx
      have hxynz : y * x ≠ 0 := ne_of_gt hxyp
      field_simp at hxy
      have h1 : (x * x + y * y) ≤ 2 * (y * x) := (div_le_iff hxyp).mp hxy
      nlinarith
  · intro hf
    rw [Set.mem_singleton_iff]
    -- We follow Evan Chen's writeup: https://web.evanchen.cc/exams/IMO-2022-notes.pdf
    let friend : ℝ+ → ℝ+ := fun x ↦ Classical.choose (hf x).exists
    have h0 : ∀ x, friend (friend x) = x := fun x ↦ by
      simp [friend]
      sorry
    have h1 : ∀ x, friend x = x := fun x ↦ by
      by_contra' H
      have h2 : ⟨2, two_pos⟩ < x * f x + x * f x := by
        obtain ⟨y, hy1, hy2⟩ := hf x
        by_contra' H2
        have h3 := hy2 x H2
        have h4 : y = friend x := by
          have h5 := Classical.choose_spec (hf x).exists
          exact (hy2 (friend x) h5).symm
        rw [h4] at h3
        exact H h3.symm
      have h6 : 1/x < f x := by sorry
      sorry
    sorry
