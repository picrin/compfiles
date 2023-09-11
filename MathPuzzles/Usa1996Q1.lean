/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import MathPuzzles.Meta.Attributes

/-!
# USA Mathematical Olympiad 1996, Problem 1

Prove that the average of the numbers n⬝sin(n π / 180)
for n ∈ {2,4,6,…,180} is 1/tan(π/180).

-/

namespace Usa1996Q1
open BigOperators

@[problem_statement]
theorem usa1996Q1 :
    (1 / (n:ℝ)) * ∑ n in Finset.range 90, (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180)
    = 1 / Real.tan (Real.pi / 180) := by
  sorry
