-- SPDX-License-Identifier: LGPL-3.0-or-later
import Mathlib

/-!
# Rectangles and tilings

Axis-parallel rectangles in the real plane, tilings of a rectangle by rectangles, and tiles of a given proportion.
-/

namespace Rectiling

/-- Axis-parallel rectangle, given by its bottom-left corner, its width and its height. -/
@[ext]
structure Rect where
  /-- Abscissa of the left side. -/
  x : ℝ
  /-- Ordinate of the bottom side. -/
  y : ℝ
  /-- Width. -/
  w : ℝ
  /-- Height. -/
  h : ℝ

namespace Rect

/-- The closed rectangle, as a set of points. -/
def closed (r : Rect) : Set (ℝ × ℝ) :=
  Set.Icc r.x (r.x + r.w) ×ˢ Set.Icc r.y (r.y + r.h)

/-- The open rectangle, as a set of points. -/
def inner (r : Rect) : Set (ℝ × ℝ) :=
  Set.Ioo r.x (r.x + r.w) ×ˢ Set.Ioo r.y (r.y + r.h)

/-- Positivity of both sides. -/
def Nondegenerate (r : Rect) : Prop :=
  0 < r.w ∧ 0 < r.h

/-- Proportion `x`: one side is `x` times the other. -/
def HasProportion (x : ℝ) (r : Rect) : Prop :=
  r.w = x * r.h ∨ r.h = x * r.w

/-- The image under the reflection exchanging the two coordinates. -/
def transpose (r : Rect) : Rect :=
  ⟨r.y, r.x, r.h, r.w⟩

/-- The rectangle with bottom-left corner at the origin and the given width and height. -/
def main (W H : ℝ) : Rect :=
  ⟨0, 0, W, H⟩

theorem mem_closed {r : Rect} {p : ℝ × ℝ} :
    p ∈ r.closed ↔ r.x ≤ p.1 ∧ p.1 ≤ r.x + r.w ∧ r.y ≤ p.2 ∧ p.2 ≤ r.y + r.h := by
  simp only [closed, Set.mem_prod, Set.mem_Icc]
  tauto

theorem mem_inner {r : Rect} {p : ℝ × ℝ} :
    p ∈ r.inner ↔ r.x < p.1 ∧ p.1 < r.x + r.w ∧ r.y < p.2 ∧ p.2 < r.y + r.h := by
  simp only [inner, Set.mem_prod, Set.mem_Ioo]
  tauto

/-- The open rectangle is the topological interior of the closed one. -/
theorem interior_closed (r : Rect) : interior r.closed = r.inner := by
  rw [closed, interior_prod_eq, interior_Icc, interior_Icc]
  rfl

theorem inner_subset_closed (r : Rect) : r.inner ⊆ r.closed := by
  intro p hp
  rw [mem_inner] at hp
  rw [mem_closed]
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩

theorem not_disjoint_inner_of_overlap {a b : Rect}
    (hx : max a.x b.x < min (a.x + a.w) (b.x + b.w))
    (hy : max a.y b.y < min (a.y + a.h) (b.y + b.h)) :
    ¬Disjoint a.inner b.inner := by
  rw [Set.not_disjoint_iff]
  refine ⟨((max a.x b.x + min (a.x + a.w) (b.x + b.w)) / 2,
    (max a.y b.y + min (a.y + a.h) (b.y + b.h)) / 2), ?_, ?_⟩
  · rw [mem_inner]
    simp only
    have h1 := le_max_left a.x b.x
    have h2 := min_le_left (a.x + a.w) (b.x + b.w)
    have h3 := le_max_left a.y b.y
    have h4 := min_le_left (a.y + a.h) (b.y + b.h)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rw [mem_inner]
    simp only
    have h1 := le_max_right a.x b.x
    have h2 := min_le_right (a.x + a.w) (b.x + b.w)
    have h3 := le_max_right a.y b.y
    have h4 := min_le_right (a.y + a.h) (b.y + b.h)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Two non-degenerate rectangles with disjoint interiors are separated by a vertical or a horizontal line. -/
theorem separated_of_disjoint {a b : Rect} (ha : a.Nondegenerate) (hb : b.Nondegenerate)
    (h : Disjoint a.inner b.inner) :
    a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x ∨ a.y + a.h ≤ b.y ∨ b.y + b.h ≤ a.y := by
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  apply not_disjoint_inner_of_overlap _ _ h
  · rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith [ha.1], h2⟩, ⟨h1, by linarith [hb.1]⟩⟩
  · rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith [ha.2], h4⟩, ⟨h3, by linarith [hb.2]⟩⟩

theorem disjoint_inner_of_separated {a b : Rect}
    (h : a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x ∨ a.y + a.h ≤ b.y ∨ b.y + b.h ≤ a.y) :
    Disjoint a.inner b.inner := by
  rw [Set.disjoint_left]
  intro p hpa hpb
  rw [mem_inner] at hpa hpb
  rcases h with h | h | h | h <;> linarith [hpa.1, hpa.2.1, hpa.2.2.1, hpa.2.2.2, hpb.1, hpb.2.1,
    hpb.2.2.1, hpb.2.2.2]

theorem not_disjoint_inner_self {a : Rect} (ha : a.Nondegenerate) : ¬Disjoint a.inner a.inner := by
  apply not_disjoint_inner_of_overlap
  · simp [ha.1]
  · simp [ha.2]

@[simp]
theorem transpose_transpose (r : Rect) : r.transpose.transpose = r :=
  rfl

theorem hasProportion_transpose {x : ℝ} {r : Rect} :
    r.transpose.HasProportion x ↔ r.HasProportion x := by
  simp [HasProportion, transpose, or_comm]

theorem nondegenerate_transpose {r : Rect} : r.transpose.Nondegenerate ↔ r.Nondegenerate := by
  simp [Nondegenerate, transpose, and_comm]

theorem mem_closed_transpose {r : Rect} {p : ℝ × ℝ} : p ∈ r.transpose.closed ↔ p.swap ∈ r.closed := by
  simp only [mem_closed, transpose, Prod.fst_swap, Prod.snd_swap]
  tauto

theorem mem_inner_transpose {r : Rect} {p : ℝ × ℝ} : p ∈ r.transpose.inner ↔ p.swap ∈ r.inner := by
  simp only [mem_inner, transpose, Prod.fst_swap, Prod.snd_swap]
  tauto

end Rect

/-- Tiling of a rectangle by a list of rectangles: the tiles have positive sides, they cover the rectangle exactly, and their interiors are pairwise disjoint. -/
structure IsTiling (R : Rect) (tiles : List Rect) : Prop where
  /-- Every tile has positive sides. -/
  nondegenerate : ∀ t ∈ tiles, t.Nondegenerate
  /-- The union of the closed tiles is the closed rectangle. -/
  cover : (⋃ t ∈ tiles, t.closed) = R.closed
  /-- The open tiles are pairwise disjoint. -/
  disjoint : tiles.Pairwise fun s t => Disjoint s.inner t.inner

/-- Tiling of a rectangle by rectangles of proportion `x`, with `x` not smaller than one. -/
structure IsSimilarTiling (x : ℝ) (R : Rect) (tiles : List Rect) : Prop extends IsTiling R tiles where
  /-- The proportion is not smaller than one. -/
  one_le : 1 ≤ x
  /-- Every tile has the given proportion. -/
  proportion : ∀ t ∈ tiles, t.HasProportion x

namespace IsTiling

variable {R : Rect} {tiles : List Rect}

theorem subset (h : IsTiling R tiles) {t : Rect} (ht : t ∈ tiles) : t.closed ⊆ R.closed := by
  rw [← h.cover]
  intro p hp
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨t, ht, hp⟩

theorem exists_mem (h : IsTiling R tiles) {p : ℝ × ℝ} (hp : p ∈ R.closed) :
    ∃ t ∈ tiles, p ∈ t.closed := by
  rw [← h.cover] at hp
  simpa using hp

/-- Two tiles of a tiling whose interiors meet are equal. -/
theorem eq_of_not_disjoint (h : IsTiling R tiles) {s t : Rect} (hs : s ∈ tiles) (ht : t ∈ tiles)
    (hst : ¬Disjoint s.inner t.inner) : s = t := by
  by_contra hne
  have : Std.Symm fun s t : Rect => Disjoint s.inner t.inner := ⟨fun _ _ h => h.symm⟩
  exact hst (h.disjoint.forall hs ht hne)

theorem perm (h : IsTiling R tiles) {tiles' : List Rect} (hp : tiles.Perm tiles') :
    IsTiling R tiles' where
  nondegenerate t ht := h.nondegenerate t (hp.mem_iff.mpr ht)
  cover := by
    rw [← h.cover]
    ext p
    simp [hp.mem_iff]
  disjoint := (hp.pairwise_iff fun h => h.symm).mp h.disjoint

/-- The transposed tiles tile the transposed rectangle. -/
theorem transpose (h : IsTiling R tiles) : IsTiling R.transpose (tiles.map Rect.transpose) where
  nondegenerate t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact Rect.nondegenerate_transpose.mpr (h.nondegenerate s hs)
  cover := by
    ext p
    have := h.cover
    rw [Set.ext_iff] at this
    have hp := this p.swap
    simp only [Set.mem_iUnion, exists_prop] at hp
    simp only [Set.mem_iUnion, exists_prop, List.mem_map, exists_exists_and_eq_and,
      Rect.mem_closed_transpose]
    exact hp
  disjoint := by
    rw [List.pairwise_map]
    refine h.disjoint.imp ?_
    intro a b hab
    rw [Set.disjoint_left] at hab ⊢
    intro p hpa hpb
    exact hab (Rect.mem_inner_transpose.mp hpa) (Rect.mem_inner_transpose.mp hpb)

end IsTiling

theorem IsSimilarTiling.transpose {x : ℝ} {R : Rect} {tiles : List Rect}
    (h : IsSimilarTiling x R tiles) : IsSimilarTiling x R.transpose (tiles.map Rect.transpose) where
  toIsTiling := h.toIsTiling.transpose
  one_le := h.one_le
  proportion t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact Rect.hasProportion_transpose.mpr (h.proportion s hs)

end Rectiling
