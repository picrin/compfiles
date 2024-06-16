/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
Bulgarian Mathematical Olympiad 1998, Problem 11

Let m,n be natural numbers such that

   A = ((m + 3)ⁿ + 1) / (3m)

is an integer. Prove that A is odd.
-/

namespace Bulgaria1998P11

snip begin

lemma even_of_add {a b : ℕ} : Even a → Even (b + a) → Even (b) := by
  rintro even_a even_b_add_a
  by_contra odd_b
  have odd_b := (@Nat.odd_iff_not_even b).mpr odd_b
  have odd_b_add_a := Even.add_odd even_a odd_b
  apply (@Nat.odd_iff_not_even (a + b)).mp
  exact odd_b_add_a
  rw [show a + b = b + a by ring]
  exact even_b_add_a

lemma mod_3_add_3_under_exponent (m n : ℕ ): ((m + 3) ^ n) ≡ (m ^ n) [MOD 3] := by
  cases n with
  | zero =>
    simp
    rfl
  | succ n =>
    have IH := @mod_3_add_3_under_exponent m n
    have first_step : (m + 3) ^ (n + 1) = (m + 3) ^ n * (m + 3) := by ring
    have third_step : (m + 3) ≡ m [MOD 3] := Nat.add_modEq_right
    have fourth_step : (m ^ n * m) = m ^ (n + 1) := by ring
    calc (m + 3) ^ (n + 1) ≡ (m + 3) ^ n * (m + 3) [MOD 3] := by rw[first_step]
    _ ≡  (m ^ n * (m + 3)) [MOD 3] := Nat.ModEq.mul IH rfl
    _ ≡  (m ^ n * m ) [MOD 3] := Nat.ModEq.mul rfl third_step
    _ ≡  m ^ (n + 1) [MOD 3] := by rw[fourth_step]

lemma zero_pow_mod_3 {m n : ℕ} (h1 : n > 0) (h2 : m ≡ 0 [MOD 3]) : m ^ n ≡ 0 [MOD 3]:= by
  match n with
  | 0 =>
    contradiction
  | 1 =>
    rw[show m ^ 1 = m by ring]
    exact h2
  | k + 2 =>
    have IH := zero_pow_mod_3 (show k + 1 > 0 by positivity) h2
    rw[show m ^ (k + 2) = m ^ (k + 1) * m by ring]
    rw[show 0 = 0 * 0 by ring]
    apply Nat.ModEq.mul
    exact IH
    exact h2

lemma one_pow_mod_3 {m n : ℕ} (h1 : n > 0) (h2 : m ≡ 1 [MOD 3]) : m ^ n ≡ 1 [MOD 3]:= by
  match n with
  | 0 =>
    contradiction
  | 1 =>
    rw[show m ^ 1 = m by ring]
    exact h2
  | k + 2 =>
    have IH := one_pow_mod_3 (show k + 1 > 0 by positivity) h2
    rw[show m ^ (k + 2) = m ^ (k + 1) * m by ring]
    rw[show 1 = 1 * 1 by ring]
    apply Nat.ModEq.mul
    exact IH
    exact h2

lemma two_mul_two_is_one_mod_3 : 2 * 2 ≡ 1 [MOD 3] := by
  have : 4 % 3 = 1 % 3 := by ring_nf
  exact this

lemma two_even_pow_mod_3 {m n : ℕ} (h1 : Even n) (h2 : m ≡ 2 [MOD 3]) : m ^ n ≡ 1 [MOD 3] := by
  match n with
  | 0 =>
    rw [show m^0 = 1 by ring]
  | 1 =>
    contradiction
  | k + 2 =>
    have k_even := even_of_add even_two h1
    have IH := two_even_pow_mod_3 k_even h2
    have inductive_step : m * m ≡ 1 [MOD 3] := by
      calc m * m ≡ 2 * 2 [MOD 3]:= Nat.ModEq.mul h2 h2
      _ ≡ 1 [MOD 3] := two_mul_two_is_one_mod_3
    rw [show m ^ (k + 2) = m ^ k * (m * m) by ring]
    rw [show 1 = 1 * 1 by ring]
    apply Nat.ModEq.mul
    exact IH
    exact inductive_step

theorem n_odd_and_m_eq_2_mod_3 (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) : Odd n ∧ m ≡ 2 [MOD 3] := by
  by_cases n_gt_zero : n > 0
  · have h_mod_3 : 0 ≡ (m ^ n + 1) [MOD 3] := by
      calc 0 ≡ 3 * (m * A) [MOD 3] := (Nat.mul_mod_right 3 (m * A)).symm
      _ ≡ (3 * m * A) [MOD 3] := by rw[show 3 * (m * A) = (3 * m * A) by ring]
      _ ≡ ((m + 3) ^ n + 1) [MOD 3] := by rw[h]
      _ ≡ (m ^ n + 1) [MOD 3] := Nat.ModEq.add (mod_3_add_3_under_exponent m n) rfl
    mod_cases mod_case : m % 3
    · have towards_contradiction : 0 ≡ 1 [MOD 3] := by
        calc 0 ≡ m ^ n + 1 [MOD 3] := h_mod_3
        _ ≡ 0 + 1 [MOD 3] := Nat.ModEq.add (zero_pow_mod_3 n_gt_zero mod_case) rfl
        _ ≡ 1 [MOD 3] := by rfl
      contradiction
    · have towards_contradiction : 0 ≡ 2 [MOD 3] := by
        rw[show 2 = 1 + 1 by ring]
        calc 0 ≡ m ^ n + 1 [MOD 3] := h_mod_3
        _ ≡ 1 + 1 [MOD 3] := Nat.ModEq.add (one_pow_mod_3 n_gt_zero mod_case) rfl
      contradiction
    · by_cases n_even : Even n
      · have towards_contradiction : 0 ≡ 2 [MOD 3] := by
          calc 0 ≡ m ^ n + 1 [MOD 3] := h_mod_3
          _ ≡ 1 + 1 [MOD 3] := Nat.ModEq.add (two_even_pow_mod_3 n_even mod_case) rfl
          _ ≡ 2 [MOD 3] := by rfl
        contradiction
      · constructor
        · apply (@Nat.odd_iff_not_even n).mpr
          exact n_even
        · exact mod_case
  · have n_eq_zero : n = 0 := by
      obtain n_lt_zero | n_eq_zero := lt_or_eq_of_le (show n ≥ 0 by positivity)
      exfalso
      apply n_gt_zero
      exact n_lt_zero
      exact n_eq_zero.symm
    rw[n_eq_zero] at h
    simp at h
    have towards_contradiction : 3 ∣ 2 := by
      use m * A
      rw[← h]
      ring
    contradiction

snip end

lemma two_n_and_rest_factorisation (m : ℕ) (even_m : Even m) (h: 0 < m) : ∃ (l : ℕ) (k : ℕ), 1 ≤ l ∧ Odd k ∧ m = 2 ^ l * k := by
  match m with
  | 0 =>
    contradiction
  | 1 =>
    contradiction
  | m + 2 =>
    have even_m2 := even_m
    obtain ⟨m', m'H⟩ := even_m
    have m'_m_relationship : m' = m/2 + 1 := sorry
    have zero_lt_m': 0 < m' := sorry
    by_cases m'_even : Even m'
    · have IH := two_n_and_rest_factorisation m' m'_even zero_lt_m'
      obtain ⟨l, k, lower_level⟩ := IH
      rw[m'_m_relationship] at lower_level
      use (l + 1)
      use k
      constructor
      · exact le_add_left (Nat.le_refl 1)
      · constructor
        · exact lower_level.right.left
        · sorry
    · use 1
      use m'
      constructor
      · exact Nat.le.refl
      · constructor
        · sorry
        · rw[m'H]
          ring


problem bulgaria1998_p11 (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  have ⟨odd_n, m_eq_2_mod_3⟩ : Odd n ∧ m ≡ 2 [MOD 3] := n_odd_and_m_eq_2_mod_3 m n A h
  by_contra even_a
  have even_a := (@Nat.even_iff_not_odd A).mpr even_a
  have even_m : Even m := sorry
