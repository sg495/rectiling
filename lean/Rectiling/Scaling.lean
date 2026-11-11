-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Geometry

/-!
# Scaling of tilings

The image of a tiling under a homothety centred at the origin, with positive ratio, is a tiling of the image of the rectangle.
-/

namespace Rectiling

namespace Rect

/-- The image under the homothety of ratio `c` centred at the origin. -/
def scale (c : ℝ) (r : Rect) : Rect :=
  ⟨c * r.x, c * r.y, c * r.w, c * r.h⟩

theorem mem_closed_scale {c : ℝ} (hc : 0 < c) {r : Rect} {p : ℝ × ℝ} :
    p ∈ (r.scale c).closed ↔ (p.1 / c, p.2 / c) ∈ r.closed := by
  simp only [mem_closed, scale, ← mul_add, le_div_iff₀ hc, div_le_iff₀ hc]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_inner_scale {c : ℝ} (hc : 0 < c) {r : Rect} {p : ℝ × ℝ} :
    p ∈ (r.scale c).inner ↔ (p.1 / c, p.2 / c) ∈ r.inner := by
  simp only [mem_inner, scale, ← mul_add, lt_div_iff₀ hc, div_lt_iff₀ hc]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem scale_main (c W H : ℝ) : (main W H).scale c = main (c * W) (c * H) := by
  simp [scale, main]

end Rect

theorem IsTiling.scale {R : Rect} {tiles : List Rect} {c : ℝ} (hc : 0 < c) (h : IsTiling R tiles) :
    IsTiling (R.scale c) (tiles.map (Rect.scale c)) where
  nondegenerate t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    have := h.nondegenerate s hs
    exact ⟨mul_pos hc this.1, mul_pos hc this.2⟩
  cover := by
    ext p
    have hcov := h.cover
    rw [Set.ext_iff] at hcov
    have hp := hcov (p.1 / c, p.2 / c)
    simp only [Set.mem_iUnion, exists_prop] at hp
    simp only [Set.mem_iUnion, exists_prop, List.mem_map, exists_exists_and_eq_and,
      Rect.mem_closed_scale hc]
    exact hp
  disjoint := by
    rw [List.pairwise_map]
    refine h.disjoint.imp ?_
    intro a b hab
    rw [Set.disjoint_left] at hab ⊢
    intro p hpa hpb
    exact hab ((Rect.mem_inner_scale hc).mp hpa) ((Rect.mem_inner_scale hc).mp hpb)

theorem IsSimilarTiling.scale {x : ℝ} {R : Rect} {tiles : List Rect} {c : ℝ} (hc : 0 < c)
    (h : IsSimilarTiling x R tiles) : IsSimilarTiling x (R.scale c) (tiles.map (Rect.scale c)) where
  toIsTiling := h.toIsTiling.scale hc
  one_le := h.one_le
  proportion t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    rcases h.proportion s hs with hp | hp
    · left
      simp only [Rect.scale, hp]
      ring
    · right
      simp only [Rect.scale, hp]
      ring

end Rectiling
