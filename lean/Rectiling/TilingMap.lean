-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.CrossSection
import Rectiling.CombinatorialMap

/-!
# The map of a tiling

The combinatorial map of a tiling of a rectangle.
Its darts are the top end and the bottom end of each tile and the two ends of an additional edge between the top side and the bottom side of the main rectangle.
The rotation sends the top end of a tile to the top end of the tile on its right with the same top, if there is one, and otherwise to the bottom end of the tile above it with the same right side, or to the additional edge on the top side of the main rectangle; and symmetrically for the bottom ends, from right to left.
Around each maximal horizontal segment this lists the tiles below it from left to right and then the tiles above it from right to left.
-/

namespace Rectiling

variable {W H : ℝ} {tl : List Rect}

local notation "Lx" e:max => Rect.x (List.get tl e)
local notation "Rx" e:max => (Rect.x (List.get tl e) + Rect.w (List.get tl e))
local notation "By" e:max => Rect.y (List.get tl e)
local notation "Ty" e:max => (Rect.y (List.get tl e) + Rect.h (List.get tl e))

open Classical in
/-- The abscissas of the vertical sides of the tiles. -/
noncomputable def sideAbscissas (tl : List Rect) : Finset ℝ :=
  (Finset.univ.image fun e : Fin tl.length => (tl.get e).x) ∪
    Finset.univ.image fun e : Fin tl.length => (tl.get e).x + (tl.get e).w

theorem left_mem_sideAbscissas (e : Fin tl.length) : Lx e ∈ sideAbscissas tl :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))

theorem right_mem_sideAbscissas (e : Fin tl.length) : Rx e ∈ sideAbscissas tl :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem (fun e : Fin tl.length => (tl.get e).x + (tl.get e).w)
    (Finset.mem_univ e))

namespace IsTiling

/-- Two tiles of a tiling whose horizontal extents overlap and whose vertical extents overlap are the same tile. -/
theorem eq_of_overlap {R : Rect} (h : IsTiling R tl) {e e' : Fin tl.length} (h1 : Lx e < Rx e')
    (h2 : Lx e' < Rx e) (h3 : By e < Ty e') (h4 : By e' < Ty e) : e = e' := by
  by_contra hne
  rcases Rect.separated_of_disjoint (h.nondegenerate _ (List.get_mem tl e))
    (h.nondegenerate _ (List.get_mem tl e')) (h.disjoint_get hne) with h5 | h5 | h5 | h5 <;> linarith

/-- Two tiles of a tiling with the same top right corner are the same tile. -/
theorem eq_of_top_right {R : Rect} (h : IsTiling R tl) {e e' : Fin tl.length} (hT : Ty e = Ty e')
    (hR : Rx e = Rx e') : e = e' := by
  have h1 := h.nondegenerate _ (List.get_mem tl e)
  have h2 := h.nondegenerate _ (List.get_mem tl e')
  exact h.eq_of_overlap (by linarith [h1.1, h2.1]) (by linarith [h1.1, h2.1]) (by linarith [h1.2, h2.2])
    (by linarith [h1.2, h2.2])

/-- Two tiles of a tiling with the same bottom left corner are the same tile. -/
theorem eq_of_bottom_left {R : Rect} (h : IsTiling R tl) {e e' : Fin tl.length} (hB : By e = By e')
    (hL : Lx e = Lx e') : e = e' := by
  have h1 := h.nondegenerate _ (List.get_mem tl e)
  have h2 := h.nondegenerate _ (List.get_mem tl e')
  exact h.eq_of_overlap (by linarith [h1.1, h2.1]) (by linarith [h1.1, h2.1]) (by linarith [h1.2, h2.2])
    (by linarith [h1.2, h2.2])

/-- The tile that contains the points just above and to the left of a point. -/
theorem exists_nw (h : IsTiling (Rect.main W H) tl) {p c : ℝ} (hp0 : 0 < p) (hpW : p ≤ W) (hc0 : 0 ≤ c)
    (hcH : c < H) : ∃ e : Fin tl.length, Lx e < p ∧ p ≤ Rx e ∧ By e ≤ c ∧ c < Ty e := by
  obtain ⟨p', hp1, hp2, hp3⟩ := exists_below_avoiding (sideAbscissas tl) hp0
  obtain ⟨c', hc1, hc2, hc3⟩ := exists_above_avoiding (sideHeights tl) hcH
  obtain ⟨t, ht, hm⟩ := h.exists_mem (p := (p', c'))
    (Rect.mem_closed.mpr (by simpa [Rect.main] using ⟨hp1.le, by linarith, by linarith, hc2.le⟩))
  obtain ⟨e, rfl⟩ := List.mem_iff_get.mp ht
  rw [Rect.mem_closed] at hm
  exact ⟨e, by linarith [hm.1], not_lt.mp fun hlt => hp3 _ (right_mem_sideAbscissas e) ⟨hm.2.1, hlt⟩,
    not_lt.mp fun hlt => hc3 _ (bottom_mem_sideHeights e) ⟨hlt, hm.2.2.1⟩, by linarith [hm.2.2.2]⟩

/-- The tile that contains the points just below and to the right of a point. -/
theorem exists_se (h : IsTiling (Rect.main W H) tl) {p c : ℝ} (hp0 : 0 ≤ p) (hpW : p < W) (hc0 : 0 < c)
    (hcH : c ≤ H) : ∃ e : Fin tl.length, Lx e ≤ p ∧ p < Rx e ∧ By e < c ∧ c ≤ Ty e := by
  obtain ⟨p', hp1, hp2, hp3⟩ := exists_above_avoiding (sideAbscissas tl) hpW
  obtain ⟨c', hc1, hc2, hc3⟩ := exists_below_avoiding (sideHeights tl) hc0
  obtain ⟨t, ht, hm⟩ := h.exists_mem (p := (p', c'))
    (Rect.mem_closed.mpr (by simpa [Rect.main] using ⟨by linarith, hp2.le, hc1.le, by linarith⟩))
  obtain ⟨e, rfl⟩ := List.mem_iff_get.mp ht
  rw [Rect.mem_closed] at hm
  exact ⟨e, not_lt.mp fun hlt => hp3 _ (left_mem_sideAbscissas e) ⟨hlt, hm.1⟩, by linarith [hm.2.1],
    by linarith [hm.2.2.1], not_lt.mp fun hlt => hc3 _ (top_mem_sideHeights e) ⟨hm.2.2.2, hlt⟩⟩

/-- A tile with no tile on its right with the same top and no tile above it with the same right side is at the top right corner of the main rectangle. -/
theorem top_right_corner (h : IsTiling (Rect.main W H) tl) (e : Fin tl.length)
    (h1 : ¬∃ e', Ty e' = Ty e ∧ Lx e' = Rx e) (h2 : ¬∃ e', By e' = Ty e ∧ Rx e' = Rx e) :
    Ty e = H ∧ Rx e = W := by
  obtain ⟨hw, hh, hx0, hxW, hy0, hyH⟩ := h.get_bounds e
  have hT : Ty e = H := by
    by_contra hne
    have hlt : Ty e < H := lt_of_le_of_ne hyH hne
    obtain ⟨q, q1, q2, q3, q4⟩ := h.exists_nw (p := Rx e) (c := Ty e) (by linarith) hxW (by linarith) hlt
    have hqb := h.get_bounds q
    have hqB : By q = Ty e := by
      refine le_antisymm q3 (not_lt.mp fun hlt' => ?_)
      have := h.eq_of_overlap (e := e) (e' := q) (by linarith) q1 (by linarith) hlt'
      subst this
      linarith
    have hqR : Rx e < Rx q := lt_of_le_of_ne q2 fun heq => h2 ⟨q, hqB, heq.symm⟩
    obtain ⟨s, s1, s2, s3, s4⟩ := h.exists_se (p := Rx e) (c := Ty e) (by linarith) (by linarith)
      (by linarith) hyH
    have hsT : Ty s = Ty e := by
      refine le_antisymm (not_lt.mp fun hlt' => ?_) s4
      have := h.eq_of_overlap (e := s) (e' := q) (by linarith) (by linarith) (by linarith) (by linarith)
      subst this
      linarith
    have hsL : Lx s = Rx e := by
      refine le_antisymm s1 (not_lt.mp fun hlt' => ?_)
      have := h.eq_of_overlap (e := s) (e' := e) hlt' (by linarith) (by linarith) (by linarith)
      subst this
      linarith
    exact h1 ⟨s, hsT, hsL⟩
  refine ⟨hT, ?_⟩
  by_contra hne
  have hlt : Rx e < W := lt_of_le_of_ne hxW hne
  obtain ⟨s, s1, s2, s3, s4⟩ := h.exists_se (p := Rx e) (c := H) (by linarith) hlt (by linarith) le_rfl
  have hsb := h.get_bounds s
  have hsL : Lx s = Rx e := by
    refine le_antisymm s1 (not_lt.mp fun hlt' => ?_)
    have := h.eq_of_overlap (e := s) (e' := e) hlt' (by linarith) (by linarith) (by linarith)
    subst this
    linarith
  exact h1 ⟨s, by linarith, hsL⟩

/-- A tile with no tile on its left with the same bottom and no tile below it with the same left side is at the bottom left corner of the main rectangle. -/
theorem bottom_left_corner (h : IsTiling (Rect.main W H) tl) (e : Fin tl.length)
    (h1 : ¬∃ e', By e' = By e ∧ Rx e' = Lx e) (h2 : ¬∃ e', Ty e' = By e ∧ Lx e' = Lx e) :
    By e = 0 ∧ Lx e = 0 := by
  obtain ⟨hw, hh, hx0, hxW, hy0, hyH⟩ := h.get_bounds e
  have hB : By e = 0 := by
    by_contra hne
    have hlt : 0 < By e := lt_of_le_of_ne hy0 (Ne.symm hne)
    obtain ⟨q, q1, q2, q3, q4⟩ := h.exists_se (p := Lx e) (c := By e) hx0 (by linarith) hlt (by linarith)
    have hqb := h.get_bounds q
    have hqT : Ty q = By e := by
      refine le_antisymm (not_lt.mp fun hlt' => ?_) q4
      have := h.eq_of_overlap (e := e) (e' := q) q2 (by linarith) hlt' (by linarith)
      subst this
      linarith
    have hqL : Lx q < Lx e := lt_of_le_of_ne q1 fun heq => h2 ⟨q, hqT, heq⟩
    obtain ⟨s, s1, s2, s3, s4⟩ := h.exists_nw (p := Lx e) (c := By e) (by linarith) (by linarith) hy0
      (by linarith)
    have hsB : By s = By e := by
      refine le_antisymm s3 (not_lt.mp fun hlt' => ?_)
      have := h.eq_of_overlap (e := s) (e' := q) (by linarith) (by linarith) (by linarith) (by linarith)
      subst this
      linarith
    have hsR : Rx s = Lx e := by
      refine le_antisymm (not_lt.mp fun hlt' => ?_) s2
      have := h.eq_of_overlap (e := s) (e' := e) (by linarith) hlt' (by linarith) (by linarith)
      subst this
      linarith
    exact h1 ⟨s, hsB, hsR⟩
  refine ⟨hB, ?_⟩
  by_contra hne
  have hlt : 0 < Lx e := lt_of_le_of_ne hx0 (Ne.symm hne)
  obtain ⟨s, s1, s2, s3, s4⟩ := h.exists_nw (p := Lx e) (c := 0) hlt (by linarith) le_rfl (by linarith)
  have hsb := h.get_bounds s
  have hsR : Rx s = Lx e := by
    refine le_antisymm (not_lt.mp fun hlt' => ?_) s2
    have := h.eq_of_overlap (e := s) (e' := e) (by linarith) hlt' (by linarith) (by linarith)
    subst this
    linarith
  exact h1 ⟨s, by linarith, hsR⟩

/-- Where the top right corner of a tile is the bottom left corner of another, a tile has that point as its bottom right corner. -/
theorem exists_nw_of (h : IsTiling (Rect.main W H) tl) {e₁ e₂ : Fin tl.length} (hc : Ty e₁ = By e₂)
    (hp : Rx e₁ = Lx e₂) : ∃ e', By e' = By e₂ ∧ Rx e' = Lx e₂ := by
  have b1 := h.get_bounds e₁
  have b2 := h.get_bounds e₂
  obtain ⟨q, q1, q2, q3, q4⟩ := h.exists_nw (p := Lx e₂) (c := By e₂) (by linarith) (by linarith)
    b2.2.2.2.2.1 (by linarith)
  have hqB : By q = By e₂ := by
    refine le_antisymm q3 (not_lt.mp fun hlt => ?_)
    have := h.eq_of_overlap (e := q) (e' := e₁) (by linarith) (by linarith) (by linarith) (by linarith)
    subst this
    linarith
  have hqR : Rx q = Lx e₂ := by
    refine le_antisymm (not_lt.mp fun hlt => ?_) q2
    have := h.eq_of_overlap (e := q) (e' := e₂) (by linarith) hlt (by linarith) (by linarith)
    subst this
    linarith
  exact ⟨q, hqB, hqR⟩

/-- Where the top right corner of a tile is the bottom left corner of another, a tile has that point as its top left corner. -/
theorem exists_se_of (h : IsTiling (Rect.main W H) tl) {e₁ e₂ : Fin tl.length} (hc : Ty e₁ = By e₂)
    (hp : Rx e₁ = Lx e₂) : ∃ e', Ty e' = Ty e₁ ∧ Lx e' = Rx e₁ := by
  have b1 := h.get_bounds e₁
  have b2 := h.get_bounds e₂
  obtain ⟨q, q1, q2, q3, q4⟩ := h.exists_se (p := Rx e₁) (c := Ty e₁) (by linarith) (by linarith)
    (by linarith) b1.2.2.2.2.2
  have hqT : Ty q = Ty e₁ := by
    refine le_antisymm (not_lt.mp fun hlt => ?_) q4
    have := h.eq_of_overlap (e := q) (e' := e₂) (by linarith) (by linarith) (by linarith) (by linarith)
    subst this
    linarith
  have hqL : Lx q = Rx e₁ := by
    refine le_antisymm q1 (not_lt.mp fun hlt => ?_)
    have := h.eq_of_overlap (e := q) (e' := e₁) hlt (by linarith) (by linarith) (by linarith)
    subst this
    linarith
  exact ⟨q, hqT, hqL⟩

/-- The tile at the top left corner of the main rectangle. -/
theorem exists_top_left (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    ∃ e : Fin tl.length, Lx e = 0 ∧ Ty e = H := by
  obtain ⟨q, q1, q2, q3, q4⟩ := h.exists_se (p := 0) (c := H) le_rfl hW hH le_rfl
  have hb := h.get_bounds q
  exact ⟨q, le_antisymm q1 hb.2.2.1, le_antisymm hb.2.2.2.2.2 q4⟩

/-- The tile at the bottom right corner of the main rectangle. -/
theorem exists_bottom_right (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    ∃ e : Fin tl.length, Rx e = W ∧ By e = 0 := by
  obtain ⟨q, q1, q2, q3, q4⟩ := h.exists_nw (p := W) (c := 0) hW le_rfl le_rfl hH
  have hb := h.get_bounds q
  exact ⟨q, le_antisymm hb.2.2.2.1 q2, le_antisymm q3 hb.2.2.2.2.1⟩

/-- The tile at the bottom left corner of the main rectangle. -/
theorem exists_bottom_left (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    ∃ e : Fin tl.length, Lx e = 0 ∧ By e = 0 := by
  obtain ⟨t, ht, hm⟩ := h.exists_mem (p := (0, 0))
    (Rect.mem_closed.mpr (by simpa [Rect.main] using ⟨hW.le, hH.le⟩))
  obtain ⟨e, rfl⟩ := List.mem_iff_get.mp ht
  rw [Rect.mem_closed] at hm
  have hb := h.get_bounds e
  exact ⟨e, le_antisymm hm.1 hb.2.2.1, le_antisymm hm.2.2.1 hb.2.2.2.2.1⟩

end IsTiling

/-- The darts of the map of a tiling with `n` tiles: for each tile its top end, marked `true`, and its bottom end, and the two ends of the additional edge, on the top side of the main rectangle, marked `true`, and on its bottom side. -/
abbrev Dart (n : ℕ) : Type :=
  Option (Fin n) × Bool

/-- The height of the horizontal line on which a dart lies. -/
def dartHeight (H : ℝ) (tl : List Rect) : Dart tl.length → ℝ
  | (some e, true) => (tl.get e).y + (tl.get e).h
  | (some e, false) => (tl.get e).y
  | (none, true) => H
  | (none, false) => 0

/-- The abscissa at which a dart starts, in the order of the rotation: top ends run from left to right and bottom ends from right to left. -/
def dartStart (W : ℝ) (tl : List Rect) : Dart tl.length → ℝ
  | (some e, true) => (tl.get e).x
  | (some e, false) => (tl.get e).x + (tl.get e).w
  | (none, true) => W
  | (none, false) => 0

/-- The abscissa at which a dart stops, in the order of the rotation. -/
def dartStop (W : ℝ) (tl : List Rect) : Dart tl.length → ℝ
  | (some e, true) => (tl.get e).x + (tl.get e).w
  | (some e, false) => (tl.get e).x
  | (none, true) => 0
  | (none, false) => W

variable (W H tl) in
/-- The rule of the rotation of the map of a tiling, as a property of a function on the darts. -/
structure IsRotation (f : Dart tl.length → Dart tl.length) : Prop where
  /-- After the top end of a tile comes the top end of the tile on its right, or the bottom end of the tile above, or the additional edge. -/
  top : ∀ e, (∃ e', f (some e, true) = (some e', true) ∧ Ty e' = Ty e ∧ Lx e' = Rx e) ∨
    (∃ e', f (some e, true) = (some e', false) ∧ By e' = Ty e ∧ Rx e' = Rx e) ∨
    (f (some e, true) = (none, true) ∧ Ty e = H ∧ Rx e = W)
  /-- After the bottom end of a tile comes the bottom end of the tile on its left, or the top end of the tile below, or the additional edge. -/
  bot : ∀ e, (∃ e', f (some e, false) = (some e', false) ∧ By e' = By e ∧ Rx e' = Lx e) ∨
    (∃ e', f (some e, false) = (some e', true) ∧ Ty e' = By e ∧ Lx e' = Lx e) ∨
    (f (some e, false) = (none, false) ∧ By e = 0 ∧ Lx e = 0)
  /-- After the additional edge on the top side comes the top end of the tile at the top left corner. -/
  poleTop : ∃ e', f (none, true) = (some e', true) ∧ Lx e' = 0 ∧ Ty e' = H
  /-- After the additional edge on the bottom side comes the bottom end of the tile at the bottom right corner. -/
  poleBot : ∃ e', f (none, false) = (some e', false) ∧ Rx e' = W ∧ By e' = 0

namespace IsRotation

variable {f : Dart tl.length → Dart tl.length}

/-- The rotation preserves the height. -/
theorem height (hf : IsRotation W H tl f) (d : Dart tl.length) :
    dartHeight H tl (f d) = dartHeight H tl d := by
  rcases d with ⟨_ | e, _ | _⟩
  · obtain ⟨e', he, -, h2⟩ := hf.poleBot
    rw [he]
    exact h2
  · obtain ⟨e', he, -, h2⟩ := hf.poleTop
    rw [he]
    exact h2
  · rcases hf.bot e with ⟨a, ha, ha1, ha2⟩ | ⟨a, ha, ha1, ha2⟩ | ⟨ha, ha1, ha2⟩ <;> rw [ha] <;>
      simp only [dartHeight] <;> linarith
  · rcases hf.top e with ⟨a, ha, ha1, ha2⟩ | ⟨a, ha, ha1, ha2⟩ | ⟨ha, ha1, ha2⟩ <;> rw [ha] <;>
      simp only [dartHeight] <;> linarith

/-- The rotation sends a dart to a dart that starts where it stops. -/
theorem start (hf : IsRotation W H tl f) (d : Dart tl.length) :
    dartStart W tl (f d) = dartStop W tl d := by
  rcases d with ⟨_ | e, _ | _⟩
  · obtain ⟨e', he, h1, -⟩ := hf.poleBot
    rw [he]
    exact h1
  · obtain ⟨e', he, h1, -⟩ := hf.poleTop
    rw [he]
    exact h1
  · rcases hf.bot e with ⟨a, ha, ha1, ha2⟩ | ⟨a, ha, ha1, ha2⟩ | ⟨ha, ha1, ha2⟩ <;> rw [ha] <;>
      simp only [dartStart, dartStop] <;> linarith
  · rcases hf.top e with ⟨a, ha, ha1, ha2⟩ | ⟨a, ha, ha1, ha2⟩ | ⟨ha, ha1, ha2⟩ <;> rw [ha] <;>
      simp only [dartStart, dartStop] <;> linarith

end IsRotation

open Classical in
/-- The rotation of the map of a tiling. -/
noncomputable def nextDart (W H : ℝ) (tl : List Rect) : Dart tl.length → Dart tl.length
  | (some e, true) =>
    if h : ∃ e', (tl.get e').y + (tl.get e').h = (tl.get e).y + (tl.get e).h ∧
        (tl.get e').x = (tl.get e).x + (tl.get e).w then (some h.choose, true)
    else if h : ∃ e', (tl.get e').y = (tl.get e).y + (tl.get e).h ∧
        (tl.get e').x + (tl.get e').w = (tl.get e).x + (tl.get e).w then (some h.choose, false)
    else (none, true)
  | (some e, false) =>
    if h : ∃ e', (tl.get e').y = (tl.get e).y ∧ (tl.get e').x + (tl.get e').w = (tl.get e).x then
      (some h.choose, false)
    else if h : ∃ e', (tl.get e').y + (tl.get e').h = (tl.get e).y ∧ (tl.get e').x = (tl.get e).x then
      (some h.choose, true)
    else (none, false)
  | (none, true) =>
    if h : ∃ e', (tl.get e').x = 0 ∧ (tl.get e').y + (tl.get e').h = H then (some h.choose, true)
    else (none, true)
  | (none, false) =>
    if h : ∃ e', (tl.get e').x + (tl.get e').w = W ∧ (tl.get e').y = 0 then (some h.choose, false)
    else (none, false)

theorem nextDart_top (h : IsTiling (Rect.main W H) tl) (e : Fin tl.length) :
    (∃ e', nextDart W H tl (some e, true) = (some e', true) ∧ Ty e' = Ty e ∧ Lx e' = Rx e) ∨
    (∃ e', nextDart W H tl (some e, true) = (some e', false) ∧ By e' = Ty e ∧ Rx e' = Rx e ∧
      ¬∃ e'', Ty e'' = Ty e ∧ Lx e'' = Rx e) ∨
    (nextDart W H tl (some e, true) = (none, true) ∧ Ty e = H ∧ Rx e = W) := by
  by_cases h1 : ∃ e', Ty e' = Ty e ∧ Lx e' = Rx e
  · exact Or.inl ⟨h1.choose, by simp only [nextDart, h1, ↓reduceDIte], h1.choose_spec⟩
  · by_cases h2 : ∃ e', By e' = Ty e ∧ Rx e' = Rx e
    · exact Or.inr (Or.inl ⟨h2.choose, by simp only [nextDart, h1, h2, ↓reduceDIte], h2.choose_spec.1,
        h2.choose_spec.2, h1⟩)
    · exact Or.inr (Or.inr ⟨by simp only [nextDart, h1, h2, ↓reduceDIte], h.top_right_corner e h1 h2⟩)

theorem nextDart_bot (h : IsTiling (Rect.main W H) tl) (e : Fin tl.length) :
    (∃ e', nextDart W H tl (some e, false) = (some e', false) ∧ By e' = By e ∧ Rx e' = Lx e) ∨
    (∃ e', nextDart W H tl (some e, false) = (some e', true) ∧ Ty e' = By e ∧ Lx e' = Lx e ∧
      ¬∃ e'', By e'' = By e ∧ Rx e'' = Lx e) ∨
    (nextDart W H tl (some e, false) = (none, false) ∧ By e = 0 ∧ Lx e = 0) := by
  by_cases h1 : ∃ e', By e' = By e ∧ Rx e' = Lx e
  · exact Or.inl ⟨h1.choose, by simp only [nextDart, h1, ↓reduceDIte], h1.choose_spec⟩
  · by_cases h2 : ∃ e', Ty e' = By e ∧ Lx e' = Lx e
    · exact Or.inr (Or.inl ⟨h2.choose, by simp only [nextDart, h1, h2, ↓reduceDIte], h2.choose_spec.1,
        h2.choose_spec.2, h1⟩)
    · exact Or.inr (Or.inr ⟨by simp only [nextDart, h1, h2, ↓reduceDIte], h.bottom_left_corner e h1 h2⟩)

/-- The rotation of the map of a tiling satisfies the rule. -/
theorem nextDart_isRotation (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    IsRotation W H tl (nextDart W H tl) where
  top e := by
    rcases nextDart_top h e with ⟨a, ha, ha1, ha2⟩ | ⟨a, ha, ha1, ha2, -⟩ | h3
    · exact Or.inl ⟨a, ha, ha1, ha2⟩
    · exact Or.inr (Or.inl ⟨a, ha, ha1, ha2⟩)
    · exact Or.inr (Or.inr h3)
  bot e := by
    rcases nextDart_bot h e with ⟨a, ha, ha1, ha2⟩ | ⟨a, ha, ha1, ha2, -⟩ | h3
    · exact Or.inl ⟨a, ha, ha1, ha2⟩
    · exact Or.inr (Or.inl ⟨a, ha, ha1, ha2⟩)
    · exact Or.inr (Or.inr h3)
  poleTop := by
    have h1 := h.exists_top_left hW hH
    exact ⟨h1.choose, by simp only [nextDart, h1, ↓reduceDIte], h1.choose_spec⟩
  poleBot := by
    have h1 := h.exists_bottom_right hW hH
    exact ⟨h1.choose, by simp only [nextDart, h1, ↓reduceDIte], h1.choose_spec⟩

/-- The top end of a tile and the bottom end of the tile whose bottom left corner is its top right corner are followed by different darts. -/
theorem nextDart_top_ne_bot (h : IsTiling (Rect.main W H) tl) {e₁ e₂ : Fin tl.length} (hc : Ty e₁ = By e₂)
    (hp : Rx e₁ = Lx e₂) : nextDart W H tl (some e₁, true) ≠ nextDart W H tl (some e₂, false) := by
  intro heq
  rcases nextDart_top h e₁ with ⟨a, ha, ha1, ha2⟩ | ⟨a, ha, ha1, ha2, ha3⟩ | ⟨ha, ha1, ha2⟩ <;>
    rcases nextDart_bot h e₂ with ⟨b, hb, hb1, hb2⟩ | ⟨b, hb, hb1, hb2, hb3⟩ | ⟨hb, hb1, hb2⟩ <;>
    rw [ha, hb] at heq <;>
    first
    | exact hb3 (h.exists_nw_of hc hp)
    | exact ha3 (h.exists_se_of hc hp)
    | simp at heq

/-- The rotation of the map of a tiling is injective. -/
theorem nextDart_injective (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    Function.Injective (nextDart W H tl) := by
  intro d₁ d₂ heq
  have hf := nextDart_isRotation h hW hH
  have hh : dartHeight H tl d₁ = dartHeight H tl d₂ := by rw [← hf.height d₁, heq, hf.height]
  have hs : dartStop W tl d₁ = dartStop W tl d₂ := by rw [← hf.start d₁, heq, hf.start]
  rcases d₁ with ⟨_ | e₁, _ | _⟩ <;> rcases d₂ with ⟨_ | e₂, _ | _⟩ <;> simp only [dartHeight, dartStop] at hh hs
  · rfl
  · exact absurd hh hH.ne
  · have := h.get_bounds e₂
    linarith
  · have := h.get_bounds e₂
    linarith
  · exact absurd hh hH.ne'
  · rfl
  · have := h.get_bounds e₂
    linarith
  · have := h.get_bounds e₂
    linarith
  · have := h.get_bounds e₁
    linarith
  · have := h.get_bounds e₁
    linarith
  · rw [h.eq_of_bottom_left hh hs]
  · exact absurd heq.symm (nextDart_top_ne_bot h hh.symm hs.symm)
  · have := h.get_bounds e₁
    linarith
  · have := h.get_bounds e₁
    linarith
  · exact absurd heq (nextDart_top_ne_bot h hh hs)
  · rw [h.eq_of_top_right hh hs]

/-- The exchange of the two ends of each edge. -/
def flipDart {n : ℕ} : Equiv.Perm (Dart n) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by
    rintro ⟨o, b⟩
    simp
  right_inv := by
    rintro ⟨o, b⟩
    simp

/-- The map of a tiling of a rectangle. -/
noncomputable def tilingMap (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    CMap (Dart tl.length) where
  σ := Equiv.ofBijective (nextDart W H tl)
    ⟨nextDart_injective h hW hH, Finite.injective_iff_surjective.mp (nextDart_injective h hW hH)⟩
  α := flipDart
  α_invol d := by
    rcases d with ⟨o, b⟩
    simp [flipDart]
  α_ne d := by
    rcases d with ⟨o, b⟩
    simp [flipDart]

variable (W H tl) in
/-- A map on the darts of a tiling whose rotation satisfies the rule and whose involution exchanges the two ends of each edge. -/
structure IsTilingMap (M : CMap (Dart tl.length)) : Prop where
  /-- The rotation satisfies the rule. -/
  rotation : IsRotation W H tl M.σ
  /-- The involution exchanges the two ends of each edge. -/
  alpha : ∀ d, M.α d = (d.1, !d.2)

/-- The map of a tiling satisfies the rule. -/
theorem tilingMap_isTilingMap (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    IsTilingMap W H tl (tilingMap h hW hH) where
  rotation := nextDart_isRotation h hW hH
  alpha _ := rfl

end Rectiling
