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

namespace Bulgaria1998P11_Adam

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

lemma mul_right {a b : ℕ} (c : ℕ) (H : a = b ) : (a * c = b * c) := by
  rw[H]

theorem Nat.add_sub_self_one_right (a : Nat) (H: 1 ≤ a) : a - 1 + 1 = a := by
  match a with
  | 0 =>
    contradiction
  | 1 =>
    rfl
  | k + 1 =>
  calc ((k + 1) - 1) + 1 = (k + (1 - 1)) + 1 := by rw[Nat.add_sub_assoc (Nat.le_refl 1) k]
  _ = k + 1 := by ring

theorem Nat.sub_add_self_right (a : Nat) (b : Nat) (H: b ≤ a) : a - b + b = a := by
  match b with
  | 0 =>
    rfl
  | l + 1 =>
    have l_le_a : l ≤ a := by linarith
    have IH := Nat.sub_add_self_right a l l_le_a
    rw[← Nat.sub_sub a l 1]
    rw[show l + 1 = 1 + l by ring]
    rw[show a - l - 1 + (1 + l) =  (a - l - 1 + 1) + l by ring]
    rw[Nat.add_sub_self_one_right (a - l)]
    exact IH
    linarith

lemma not_one_le_k {k : ℕ} (h : ¬1 ≤ k) : k = 0 := by
  simp_all only [not_le, Nat.lt_one_iff]

lemma two_le_pow_two (l : ℕ) : 2 ≤ 2 ^ (l + 1) := by
  match l with
    | 0 =>
      simp
    | 1 =>
      simp
    | l + 1 =>
      have IH := two_le_pow_two l
      ring_nf at IH
      rw[show 2 ^ (l + 1 + 1) = (2 ^ l * 2) * 2 by ring_nf]
      linarith

lemma two_n_and_rest_factorisation (m : ℕ) (even_m : Even m) (h: 0 < m) : ∃ (l : ℕ) (m₁ : ℕ), 1 ≤ l ∧ Odd m₁ ∧ m = 2 ^ l * m₁ := by
  match m with
  | 0 =>
    contradiction
  | 1 =>
    contradiction
  | m + 2 =>
    have even_m2 := even_m
    obtain ⟨m', m'H⟩ := even_m
    have m_m'_relationship : m = 2 * m' - 2 := by
      rw[show 2 * m' = m' + m' by ring]
      rw[← m'H]
      rw[Nat.add_sub_self_right m 2]
    have one_le_m' : 1 ≤ m' := by
      rename_i m_1
      subst m_m'_relationship
      simp_all only [pos_add_self_iff, even_add_self]
      exact h
    have m'_m_relationship : m' = m /2 + 1 := by
      rw[m_m'_relationship]
      rw[← Nat.mul_sub_left_distrib 2 m' 1]
      field_simp
    have zero_lt_m': 0 < m' := by linarith
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
        · obtain ⟨_, ⟨k_odd: Odd k, lower_level_statement : m / 2 + 1 = 2 ^ l * k ⟩⟩ := lower_level
          have two_le_k : 2 ≤ 2 ^ (l + 1) * k := by
            have one_le_k : 1 ≤ k := by
              by_contra k_zero
              have k_zero : k = 0 := not_one_le_k k_zero
              have even_k : Even 0 := even_zero
              rw[← k_zero] at even_k
              exact (Nat.even_iff_not_odd.mp even_k) k_odd
            have two_le_expr : 2 ≤ 2 ^ (l + 1) := two_le_pow_two l
            exact Nat.mul_le_mul two_le_expr one_le_k
          have lower_level_statement_2 : (m / 2 + 1) * 2 = (2 ^ l * k) * 2 := mul_right 2 lower_level_statement
          calc m + 2 = (2 * m' - 2) + 2 := by rw[m_m'_relationship]
          _ = (m' * 2 - 2) + 2 := by ring_nf
          _ = ((m / 2 + 1) * 2 - 2) + 2 := by rw[m'_m_relationship]
          _ = ((2 ^ l * k) * 2 - 2) + 2 := by rw[lower_level_statement_2]
          _ = (2 ^ (l + 1) * k - 2) + 2 := by ring_nf
          _ = 2 ^ (l + 1) * k := Nat.sub_add_self_right (2 ^ (l + 1) * k) 2 two_le_k
    · use 1
      use m'
      constructor
      · exact Nat.le.refl
      · constructor
        · exact Nat.odd_iff_not_even.mpr m'_even
        · rw[m'H]
          ring
snip end

problem bulgaria1998_p11 (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  have ⟨odd_n, m_eq_2_mod_3⟩ : Odd n ∧ m ≡ 2 [MOD 3] := n_odd_and_m_eq_2_mod_3 m n A h
  by_contra even_a
  have even_a := (@Nat.even_iff_not_odd A).mpr even_a
  have even_m : Even m := sorry
  have zero_lt_m : 0 < m := sorry
  obtain ⟨l, m₁, ⟨one_le_l, odd_m₁, m_factorisation⟩⟩ := two_n_and_rest_factorisation m even_m zero_lt_m
  by_cases l_eq_one : (l = 1)
  · rw [l_eq_one] at m_factorisation
    ring_nf at m_factorisation
    have : m₁ ≡ 1 [MOD 4] ∨ m₁ ≡ 3 [MOD 4] := by
      obtain ⟨a, aH⟩ := odd_m₁
      obtain even_a | odd_a := Nat.even_or_odd a
      · obtain ⟨b, bH⟩ := even_a
        left
        rw[aH]
        rw[bH]
        dsimp [Nat.ModEq]
        ring_nf
        simp
      · obtain ⟨b, bH⟩ := odd_a
        right
        rw[aH]
        rw[bH]
        dsimp [Nat.ModEq]
        ring_nf
        simp
    have m_eq_2_mod_4 : m ≡ 2 [MOD 4] := by
      obtain left | right := this
      · rw[m_factorisation]
        rw[show 2 = 1 * 2 by rfl]
        apply Nat.ModEq.mul
        exact left
        ring_nf
        rfl
      · rw[m_factorisation]
        --dsimp[Nat.ModEq] at right
        --dsimp[Nat.ModEq]
        calc m₁ * 2 ≡ 3 * 2 [MOD 4] := Nat.ModEq.mul right (show 2 ≡ 2 [MOD 4] by rfl)
          _ ≡ 2 [MOD 4] := (show 3 * 2 ≡ 2 [MOD 4] by rfl)
    sorry
  ·
    have one_lt_l : 1 < l := by
      obtain left | right := LE.le.lt_or_eq one_le_l
      exact left
      exfalso
      apply l_eq_one
      exact right.symm
    have l_eq_2 : l = 2 := sorry
    have m_eq_4m₁ : m = 4*m₁ := sorry
    have m₁_eq_2_mod3 : m₁ ≡ 2 [MOD 3] := sorry
    have m₁_eq_5_mod6 : m₁ ≡ 5 [MOD 6] := sorry

    -- from Thue's lemma
    have k : ℕ := sorry
    have k_constraints : k = 1 ∨ k = 2 ∨ k = 3 := sorry
    have x : ℕ := sorry
    have y : ℕ := sorry
    have expression : 3 * x ^ 2 + y ^ 2 = k * m₁ := sorry

  -- we then proceed to get contradiction for each k separately
    sorry
