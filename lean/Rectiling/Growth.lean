-- SPDX-License-Identifier: LGPL-3.0-or-later
import Mathlib

/-!
# The rate of growth of the bound

The number `2 (3n)! / ((2n + 1)! (n + 1)!)` of rooted non-separable planar maps with `n + 1` edges is at most `(27 / 4) ^ n`, and a sequence bounded by `n 2 ^ (n - 1)` times this number has upper limit of its `n`-th roots at most `27 / 2`.
-/

namespace Rectiling

/-- The number `2 (3n)! / ((2n + 1)! (n + 1)!)`. -/
def tutteM (n : ℕ) : ℕ :=
  2 * (3 * n).factorial / ((2 * n + 1).factorial * (n + 1).factorial)

theorem tutteM_le_choose {n : ℕ} (hn : 1 ≤ n) : tutteM n ≤ (3 * n).choose n := by
  unfold tutteM
  apply Nat.div_le_of_le_mul
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
  have h2 : 3 * n - n = 2 * n := by omega
  rw [h2] at h1
  rw [Nat.factorial_succ (2 * n), Nat.factorial_succ n, ← h1]
  have h3 : 2 ≤ (2 * n + 1) * (n + 1) := by nlinarith
  calc 2 * ((3 * n).choose n * n.factorial * (2 * n).factorial)
      ≤ (2 * n + 1) * (n + 1) * ((3 * n).choose n * n.factorial * (2 * n).factorial) :=
        Nat.mul_le_mul_right _ h3
    _ = (2 * n + 1) * (2 * n).factorial * ((n + 1) * n.factorial) * (3 * n).choose n := by ring

theorem choose_three_mul_le (n : ℕ) : ((3 * n).choose n : ℝ) * 4 ^ n ≤ 27 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (3 * n).choose n * (n ^ n * (2 * n) ^ (2 * n)) ≤ (3 * n) ^ (3 * n) := by
    have h := add_pow n (2 * n) (3 * n)
    have h2 : n + 2 * n = 3 * n := by ring
    rw [h2] at h
    rw [h]
    have h4 := Finset.single_le_sum (f := fun m => n ^ m * (2 * n) ^ (3 * n - m) * (3 * n).choose m)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (show n < 3 * n + 1 by omega))
    have h3 : 3 * n - n = 2 * n := by omega
    simp only [h3] at h4
    calc (3 * n).choose n * (n ^ n * (2 * n) ^ (2 * n)) = n ^ n * (2 * n) ^ (2 * n) * (3 * n).choose n := by
          ring
      _ ≤ _ := h4
  have h2 : ((3 * n).choose n : ℝ) * ((n : ℝ) ^ n * (2 * n) ^ (2 * n)) ≤ (3 * n : ℝ) ^ (3 * n) := by
    exact_mod_cast h1
  have hn' : (0 : ℝ) < (n : ℝ) ^ (3 * n) := by positivity
  have e0 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  have e1 : (n : ℝ) ^ n * (2 * n) ^ (2 * n) = 4 ^ n * (n : ℝ) ^ (3 * n) := by
    rw [mul_pow, e0]
    ring
  have e2 : (3 * n : ℝ) ^ (3 * n) = 27 ^ n * (n : ℝ) ^ (3 * n) := by
    rw [mul_pow, pow_mul]
    norm_num
  rw [e1, e2, ← mul_assoc] at h2
  exact le_of_mul_le_mul_right h2 hn'

/-- The number of rooted non-separable planar maps with `n + 1` edges is at most `(27 / 4) ^ n`. -/
theorem tutteM_le {n : ℕ} (hn : 1 ≤ n) : (tutteM n : ℝ) ≤ (27 / 4) ^ n := by
  have h1 : (tutteM n : ℝ) ≤ (3 * n).choose n := by exact_mod_cast tutteM_le_choose hn
  have h2 := choose_three_mul_le n
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2

/-- A sequence bounded by `n 2 ^ (n - 1)` times the number of rooted non-separable planar maps with `n + 1` edges is at most `n (27 / 2) ^ n`. -/
theorem le_of_le_tutteM {a : ℕ → ℕ} (h : ∀ n, 1 ≤ n → a n ≤ n * 2 ^ (n - 1) * tutteM n) {n : ℕ} (hn : 1 ≤ n) :
    (a n : ℝ) ≤ n * (27 / 2) ^ n := by
  have h1 : (a n : ℝ) ≤ n * 2 ^ (n - 1) * tutteM n := by exact_mod_cast h n hn
  have h2 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
  have h3 := tutteM_le hn
  have h4 : (2 : ℝ) ^ n * (27 / 4) ^ n = (27 / 2) ^ n := by
    rw [← mul_pow]
    norm_num
  calc (a n : ℝ) ≤ n * 2 ^ (n - 1) * tutteM n := h1
    _ ≤ n * 2 ^ n * (27 / 4) ^ n := by gcongr
    _ = n * (27 / 2) ^ n := by rw [mul_assoc, h4]

/-- A sequence bounded by `n 2 ^ (n - 1)` times the number of rooted non-separable planar maps with `n + 1` edges has upper limit of its `n`-th roots at most `27 / 2`. -/
theorem limsup_le_of_le_tutteM {a : ℕ → ℕ} (h : ∀ n, 1 ≤ n → a n ≤ n * 2 ^ (n - 1) * tutteM n) :
    Filter.limsup (fun n => (a n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop ≤ 27 / 2 := by
  have hle : ∀ᶠ n : ℕ in Filter.atTop, (a n : ℝ) ^ (1 / (n : ℝ)) ≤ (n : ℝ) ^ (1 / (n : ℝ)) * (27 / 2) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    calc (a n : ℝ) ^ (1 / (n : ℝ)) ≤ ((n : ℝ) * (27 / 2) ^ n) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (le_of_le_tutteM h hn) (by positivity)
      _ = (n : ℝ) ^ (1 / (n : ℝ)) * ((27 / 2 : ℝ) ^ n) ^ (1 / (n : ℝ)) :=
          Real.mul_rpow (Nat.cast_nonneg _) (by positivity)
      _ = (n : ℝ) ^ (1 / (n : ℝ)) * (27 / 2) := by
          rw [one_div, Real.pow_rpow_inv_natCast (by norm_num) (by omega)]
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ)) * (27 / 2)) Filter.atTop (nhds (27 / 2)) := by
    have := (tendsto_rpow_div.comp tendsto_natCast_atTop_atTop).mul_const (27 / 2 : ℝ)
    simpa using this
  have hco : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ)) :=
    (Filter.isBoundedUnder_of ⟨0, fun n => by positivity⟩ :
      Filter.IsBoundedUnder (· ≥ ·) Filter.atTop fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))).isCoboundedUnder_le
  calc Filter.limsup (fun n => (a n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ)) * (27 / 2)) Filter.atTop :=
        Filter.limsup_le_limsup hle hco ht.isBoundedUnder_le
    _ = 27 / 2 := ht.limsup_eq

end Rectiling
