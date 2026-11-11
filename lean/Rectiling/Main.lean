-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Completeness
import Rectiling.Scaling
import Rectiling.Solver

/-!
# Correctness of the reference method

The proportions reported by the reference method, over all the placement sequences that the search enumerates, are the proportions of the tilings of the main rectangle, provided that the search meets no singular situation and no sequence whose aspect ratio does not depend on the proportion.
-/

namespace Rectiling

/-- The proportion `x` is reported for `n` tiles and a main rectangle of width `a` and height `b`: some enumerated placement sequence realises it. -/
def Reported (P : Primitives) (a b : ℤ) (n : ℕ) (x : ℝ) : Prop :=
  ∃ path, Complete n path ∧ (a = b → FirstWide path) ∧ x ∈ (solve P a b path).feasible

/-- The search is certified: no enumerated placement sequence is singular or has an aspect ratio that does not depend on the proportion. -/
def Certified (P : Primitives) (a b : ℤ) (n : ℕ) : Prop :=
  ∀ path, Complete n path → (a = b → FirstWide path) →
    (solve P a b path).singular = 0 ∧ (solve P a b path).constant = false

/-- **Soundness of the reference method.** Every reported proportion is the proportion of a tiling of the `a × b` rectangle by `n` rectangles. -/
theorem reported_sound (P : Primitives) {a b : ℤ} (hb : 0 < b) {n : ℕ} {x : ℝ}
    (h : Reported P a b n x) :
    ∃ tl : List Rect, IsSimilarTiling x (Rect.main a b) tl ∧ tl.length = n := by
  obtain ⟨path, hpath, -, hx⟩ := h
  obtain ⟨hx1, fresh, hsat⟩ := solve_sound P hb.ne' hpath hx
  obtain ⟨htiling, hlen⟩ := soundness fresh hx1 hpath hsat
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hscaled := htiling.scale hbR
  rw [Rect.scale_main, mul_one, mul_div_cancel₀ _ hbR.ne'] at hscaled
  exact ⟨_, hscaled, by rw [List.length_map, hlen]⟩

/-- **Completeness of the reference method.** If the search is certified, the proportion of every tiling of the `a × b` rectangle by `n` rectangles is reported. -/
theorem reported_complete (P : Primitives) {a b : ℤ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    {tl : List Rect} (h : IsSimilarTiling x (Rect.main a b) tl)
    (hcert : Certified P a b tl.length) : Reported P a b tl.length x := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hscaled := h.scale (inv_pos.mpr hbR)
  rw [Rect.scale_main, inv_mul_cancel₀ hbR.ne', inv_mul_eq_div] at hscaled
  have hlen : (tl.map (Rect.scale (b : ℝ)⁻¹)).length = tl.length := List.length_map _
  by_cases hab : a = b
  · have hone : (a : ℝ) / b = 1 := by
      rw [hab]
      exact div_self hbR.ne'
    have hscaled' := hscaled
    rw [hone] at hscaled'
    obtain ⟨path, fresh, hpath, hwide, hsat, -⟩ := completeness_square one_pos hscaled'
    rw [hlen] at hpath
    have hsat' : Satisfies x fresh (initial ((a : ℝ) / b) 1) 0 path := by
      rw [hone]
      exact hsat
    obtain ⟨hs, hc⟩ := hcert path hpath fun _ => hwide
    exact ⟨path, hpath, fun _ => hwide, solve_complete P hb.ne' hpath hs hc h.one_le hsat'⟩
  · obtain ⟨path, fresh, hpath, hsat, -, -⟩ := completeness (div_pos haR hbR) one_pos hscaled
    rw [hlen] at hpath
    obtain ⟨hs, hc⟩ := hcert path hpath fun h => absurd h hab
    exact ⟨path, hpath, fun h => absurd h hab, solve_complete P hb.ne' hpath hs hc h.one_le hsat⟩

/-- **Correctness of the reference method.** If the search for `n` tiles is certified, the reported proportions are exactly the proportions of the tilings of the `a × b` rectangle by `n` rectangles. -/
theorem reported_iff (P : Primitives) {a b : ℤ} (ha : 0 < a) (hb : 0 < b) {n : ℕ}
    (hcert : Certified P a b n) (x : ℝ) :
    Reported P a b n x ↔
      ∃ tl : List Rect, IsSimilarTiling x (Rect.main a b) tl ∧ tl.length = n := by
  constructor
  · exact reported_sound P hb
  · rintro ⟨tl, htl, rfl⟩
    exact reported_complete P ha hb htl hcert

end Rectiling
