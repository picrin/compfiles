/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic


/-!
Bulgarian Mathematical Olympiad 1998, Problem 11

Let m,n be natural numbers such that

   A = ((m + 3)ⁿ + 1) / (3m)

is an integer. Prove that A is odd.
-/

namespace Bulgaria1998P11



lemma eq_implies_eq_mod_3 {a b : ℕ} (h : a = b) : a ≡ b [MOD 3] := by
  rw[h]

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

theorem n_odd (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) : Odd n := by
  have internal_mod_3 : (m + 3) ^ n = (m + 3) % 3 ^ (n % 3) := by
    sorry
  have h_mod_3 : 0 ≡ (m ^ n + 1) [MOD 3] := by
    calc 0 ≡ 3 * (m * A) [MOD 3] := (Nat.mul_mod_right 3 (m * A)).symm
    _ ≡ (3 * m * A) [MOD 3] := by rw[show 3 * (m * A) = (3 * m * A) by ring]
    _ ≡ ((m + 3) ^ n + 1) [MOD 3] := by rw[h]
    _ ≡ (m ^ n + 1) [MOD 3] := Nat.ModEq.add (mod_3_add_3_under_exponent m n) rfl
  mod_cases mod_case : m % 3
  · have towards_contradiction : 0 ≡ 1 [MOD 3] := by
      calc 0 ≡ m ^ n + 1 [MOD 3] := h_mod_3
      _ ≡ 0 + 1 [MOD 3] := sorry
      _ ≡ 1 [MOD 3] := by rfl
    contradiction
  · sorry
  · sorry

lemma mod_plus_pow (m n : ℕ) : (m + 3)^n % 3 = m^n % 3 := by
  induction' n with pn hpn
  · simp only [Nat.zero_eq, pow_zero, Nat.one_mod]
  · rw [Nat.pow_succ']
    have h1 : (m + 3) * (m + 3) ^ pn = m * (m + 3) ^ pn + 3 * (m + 3) ^ pn := by ring
    rw [h1]
    have h2 : 3 * (m + 3) ^ pn % 3 = 0 := Nat.mul_mod_right 3 _
    rw[Nat.add_mod, h2, add_zero, Nat.mod_mod, Nat.pow_succ']
    exact Nat.ModEq.mul rfl hpn

lemma foo1 (m n : ℕ) (ho : Odd m) : (m + 3) ^ n.succ % 2 = 0 := by
  cases' ho with w hw
  rw[hw, Nat.pow_succ, show 2 * w + 1 + 3 = 2 * (w + 2) by ring, Nat.mul_mod,
     Nat.mul_mod_right, mul_zero, Nat.zero_mod]
