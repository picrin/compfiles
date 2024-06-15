import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

lemma mod_3_add_3_under_exponent (m n : ℕ ) : (2 * n ≡ 0 [MOD 3]) := by
  cases n with
  | zero =>
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

#check mod_3_add_3_under_exponent

lemma soundness_issue : False := by
  have A : 2 * 1 ≡ 0 [MOD 3] := mod_3_add_3_under_exponent 0 1
  contradiction

#check soundness_issue
