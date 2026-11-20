-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Geometry

/-!
# Horizontal sections of a tiling

The widths of the tiles of a tiling of a rectangle that meet a horizontal line add up to the width of the rectangle.
Consequently the tiles whose bottom sides lie at a given height have the same total width as those whose top sides lie at that height.
-/

namespace Rectiling

variable {W H : ℝ} {tl : List Rect}

/-- The sides of a tile of a tiling are positive and the tile lies in the main rectangle. -/
theorem IsTiling.get_bounds (h : IsTiling (Rect.main W H) tl) (e : Fin tl.length) :
    0 < (tl.get e).w ∧ 0 < (tl.get e).h ∧ 0 ≤ (tl.get e).x ∧ (tl.get e).x + (tl.get e).w ≤ W ∧
      0 ≤ (tl.get e).y ∧ (tl.get e).y + (tl.get e).h ≤ H := by
  have hm := List.get_mem tl e
  obtain ⟨hw, hh⟩ := h.nondegenerate _ hm
  have h1 := h.subset hm (a := ((tl.get e).x, (tl.get e).y))
    (Rect.mem_closed.mpr ⟨le_rfl, by simp only; linarith, le_rfl, by simp only; linarith⟩)
  have h2 := h.subset hm (a := ((tl.get e).x + (tl.get e).w, (tl.get e).y + (tl.get e).h))
    (Rect.mem_closed.mpr ⟨by simp only; linarith, le_rfl, by simp only; linarith, le_rfl⟩)
  rw [Rect.mem_closed] at h1 h2
  simp only [Rect.main, zero_add] at h1 h2
  exact ⟨hw, hh, h1.1, h2.2.1, h1.2.2.1, h2.2.2.2⟩

/-- Two tiles of a tiling at different positions of the list have disjoint interiors. -/
theorem IsTiling.disjoint_get {R : Rect} (h : IsTiling R tl) {e e' : Fin tl.length} (hne : e ≠ e') :
    Disjoint (tl.get e).inner (tl.get e').inner := by
  have hp := List.pairwise_iff_get.mp h.disjoint
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hp e e' hlt
  · exact (hp e' e hlt).symm

/-- On a horizontal line that contains no horizontal side of a tile, the widths of the tiles that the line crosses add up to the width of the main rectangle. -/
theorem IsTiling.sum_generic (h : IsTiling (Rect.main W H) tl) (hW : 0 ≤ W) {c : ℝ} (hc0 : 0 ≤ c)
    (hcH : c ≤ H) (hgen : ∀ e : Fin tl.length, c ≠ (tl.get e).y ∧ c ≠ (tl.get e).y + (tl.get e).h) :
    ∑ e : Fin tl.length,
      (if (tl.get e).y < c ∧ c < (tl.get e).y + (tl.get e).h then (tl.get e).w else 0) = W := by
  classical
  rw [← Finset.sum_filter]
  set S := Finset.univ.filter fun e : Fin tl.length => (tl.get e).y < c ∧ c < (tl.get e).y + (tl.get e).h
    with hS
  have hmem : ∀ e, e ∈ S ↔ (tl.get e).y < c ∧ c < (tl.get e).y + (tl.get e).h := by simp [hS]
  have hnn : ∀ e ∈ S, 0 ≤ (tl.get e).w := fun e _ => (h.get_bounds e).1.le
  have hsum0 : 0 ≤ ∑ e ∈ S, (tl.get e).w := Finset.sum_nonneg hnn
  have hcover : Set.Icc 0 W ⊆ ⋃ e ∈ S, Set.Icc (tl.get e).x ((tl.get e).x + (tl.get e).w) := by
    intro u hu
    obtain ⟨t, ht, hp⟩ := h.exists_mem (p := (u, c))
      (Rect.mem_closed.mpr (by simpa [Rect.main] using ⟨hu.1, hu.2, hc0, hcH⟩))
    obtain ⟨e, rfl⟩ := List.mem_iff_get.mp ht
    rw [Rect.mem_closed] at hp
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨e, (hmem e).mpr ⟨lt_of_le_of_ne hp.2.2.1 (Ne.symm (hgen e).1), lt_of_le_of_ne hp.2.2.2 (hgen e).2⟩,
      hp.1, hp.2.1⟩
  have hsub : (⋃ e ∈ S, Set.Ioo (tl.get e).x ((tl.get e).x + (tl.get e).w)) ⊆ Set.Icc 0 W := by
    intro u hu
    simp only [Set.mem_iUnion, exists_prop] at hu
    obtain ⟨e, -, hu⟩ := hu
    have hb := h.get_bounds e
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hdisj : (S : Set (Fin tl.length)).PairwiseDisjoint fun e =>
      Set.Ioo (tl.get e).x ((tl.get e).x + (tl.get e).w) := by
    intro e he e' he' hne
    rw [Function.onFun, Set.disjoint_left]
    intro u hu hu'
    have h1 := (hmem e).mp he
    have h2 := (hmem e').mp he'
    exact Set.disjoint_left.mp (h.disjoint_get hne)
      ((Rect.mem_inner (p := (u, c))).mpr ⟨hu.1, hu.2, h1.1, h1.2⟩) (Rect.mem_inner.mpr ⟨hu'.1, hu'.2, h2.1, h2.2⟩)
  have h1 : ENNReal.ofReal W ≤ ENNReal.ofReal (∑ e ∈ S, (tl.get e).w) := by
    calc ENNReal.ofReal W = MeasureTheory.volume (Set.Icc 0 W) := by rw [Real.volume_Icc, sub_zero]
      _ ≤ MeasureTheory.volume (⋃ e ∈ S, Set.Icc (tl.get e).x ((tl.get e).x + (tl.get e).w)) :=
        MeasureTheory.measure_mono hcover
      _ ≤ ∑ e ∈ S, MeasureTheory.volume (Set.Icc (tl.get e).x ((tl.get e).x + (tl.get e).w)) :=
        MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ e ∈ S, ENNReal.ofReal (tl.get e).w := by simp [Real.volume_Icc]
      _ = ENNReal.ofReal (∑ e ∈ S, (tl.get e).w) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
  have h2 : ENNReal.ofReal (∑ e ∈ S, (tl.get e).w) ≤ ENNReal.ofReal W := by
    calc ENNReal.ofReal (∑ e ∈ S, (tl.get e).w) = ∑ e ∈ S, ENNReal.ofReal (tl.get e).w :=
        ENNReal.ofReal_sum_of_nonneg hnn
      _ = ∑ e ∈ S, MeasureTheory.volume (Set.Ioo (tl.get e).x ((tl.get e).x + (tl.get e).w)) := by
        simp [Real.volume_Ioo]
      _ = MeasureTheory.volume (⋃ e ∈ S, Set.Ioo (tl.get e).x ((tl.get e).x + (tl.get e).w)) :=
        (MeasureTheory.measure_biUnion_finset hdisj fun _ _ => measurableSet_Ioo).symm
      _ ≤ MeasureTheory.volume (Set.Icc 0 W) := MeasureTheory.measure_mono hsub
      _ = ENNReal.ofReal W := by rw [Real.volume_Icc, sub_zero]
  exact le_antisymm ((ENNReal.ofReal_le_ofReal_iff hW).mp h2) ((ENNReal.ofReal_le_ofReal_iff hsum0).mp h1)

/-- A point above `c` and below `d` with no element of a finite set between `c` and it. -/
theorem exists_above_avoiding (Y : Finset ℝ) {c d : ℝ} (hcd : c < d) :
    ∃ c', c < c' ∧ c' < d ∧ ∀ y ∈ Y, ¬(c < y ∧ y ≤ c') := by
  classical
  have hZ : (insert d (Y.filter (c < ·))).Nonempty := Finset.insert_nonempty _ _
  have hm : c < (insert d (Y.filter (c < ·))).min' hZ := by
    rcases Finset.mem_insert.mp (Finset.min'_mem _ hZ) with h | h
    · rw [h]
      exact hcd
    · exact (Finset.mem_filter.mp h).2
  refine ⟨(c + (insert d (Y.filter (c < ·))).min' hZ) / 2, by linarith, ?_, ?_⟩
  · have := Finset.min'_le _ d (Finset.mem_insert_self d (Y.filter (c < ·)))
    linarith
  · rintro y hy ⟨h1, h2⟩
    have := Finset.min'_le _ y (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hy, h1⟩) : y ∈ insert d _)
    linarith

/-- A point below `c` and above `d` with no element of a finite set between it and `c`. -/
theorem exists_below_avoiding (Y : Finset ℝ) {c d : ℝ} (hdc : d < c) :
    ∃ c', d < c' ∧ c' < c ∧ ∀ y ∈ Y, ¬(c' ≤ y ∧ y < c) := by
  classical
  obtain ⟨c', h1, h2, h3⟩ := exists_above_avoiding (Y.image fun y => -y) (neg_lt_neg hdc)
  refine ⟨-c', by linarith, by linarith, fun y hy hh => h3 (-y) (Finset.mem_image_of_mem _ hy) ?_⟩
  exact ⟨by linarith [hh.2], by linarith [hh.1]⟩

open Classical in
/-- The ordinates of the horizontal sides of the tiles. -/
noncomputable def sideHeights (tl : List Rect) : Finset ℝ :=
  (Finset.univ.image fun e : Fin tl.length => (tl.get e).y) ∪
    Finset.univ.image fun e : Fin tl.length => (tl.get e).y + (tl.get e).h

theorem bottom_mem_sideHeights (e : Fin tl.length) : (tl.get e).y ∈ sideHeights tl :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))

theorem top_mem_sideHeights (e : Fin tl.length) : (tl.get e).y + (tl.get e).h ∈ sideHeights tl :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem (fun e : Fin tl.length => (tl.get e).y + (tl.get e).h)
    (Finset.mem_univ e))

/-- Below the top of the main rectangle, the widths of the tiles that meet the points just above a horizontal line add up to the width of the main rectangle. -/
theorem IsTiling.sum_above (h : IsTiling (Rect.main W H) tl) (hW : 0 ≤ W) {c : ℝ} (hc0 : 0 ≤ c)
    (hcH : c < H) :
    ∑ e : Fin tl.length,
      (if (tl.get e).y ≤ c ∧ c < (tl.get e).y + (tl.get e).h then (tl.get e).w else 0) = W := by
  obtain ⟨c', h1, h2, h3⟩ := exists_above_avoiding (sideHeights tl) hcH
  have hb := fun e => h3 _ (bottom_mem_sideHeights (tl := tl) e)
  have ht := fun e => h3 _ (top_mem_sideHeights (tl := tl) e)
  rw [← h.sum_generic hW (c := c') (by linarith) h2.le fun e =>
    ⟨fun he => hb e ⟨by linarith, he.ge⟩, fun he => ht e ⟨by linarith, he.ge⟩⟩]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hiff : ((tl.get e).y ≤ c ∧ c < (tl.get e).y + (tl.get e).h) ↔
      ((tl.get e).y < c' ∧ c' < (tl.get e).y + (tl.get e).h) := by
    constructor
    · rintro ⟨a, b⟩
      exact ⟨by linarith, not_le.mp fun hle => ht e ⟨b, hle⟩⟩
    · rintro ⟨a, b⟩
      exact ⟨not_lt.mp fun hlt => hb e ⟨hlt, a.le⟩, by linarith⟩
  simp only [hiff]

/-- Above the bottom of the main rectangle, the widths of the tiles that meet the points just below a horizontal line add up to the width of the main rectangle. -/
theorem IsTiling.sum_below (h : IsTiling (Rect.main W H) tl) (hW : 0 ≤ W) {c : ℝ} (hc0 : 0 < c)
    (hcH : c ≤ H) :
    ∑ e : Fin tl.length,
      (if (tl.get e).y < c ∧ c ≤ (tl.get e).y + (tl.get e).h then (tl.get e).w else 0) = W := by
  obtain ⟨c', h1, h2, h3⟩ := exists_below_avoiding (sideHeights tl) hc0
  have hb := fun e => h3 _ (bottom_mem_sideHeights (tl := tl) e)
  have ht := fun e => h3 _ (top_mem_sideHeights (tl := tl) e)
  rw [← h.sum_generic hW (c := c') h1.le (by linarith) fun e =>
    ⟨fun he => hb e ⟨he.le, by linarith⟩, fun he => ht e ⟨he.le, by linarith⟩⟩]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hiff : ((tl.get e).y < c ∧ c ≤ (tl.get e).y + (tl.get e).h) ↔
      ((tl.get e).y < c' ∧ c' < (tl.get e).y + (tl.get e).h) := by
    constructor
    · rintro ⟨a, b⟩
      exact ⟨not_le.mp fun hle => hb e ⟨hle, a⟩, by linarith⟩
    · rintro ⟨a, b⟩
      exact ⟨by linarith, not_lt.mp fun hlt => ht e ⟨b.le, hlt⟩⟩
  simp only [hiff]

theorem ite_level {y h w c : ℝ} (hh : 0 < h) :
    (if y = c then w else 0) - (if y + h = c then w else 0) =
      (if y ≤ c ∧ c < y + h then w else 0) - (if y < c ∧ c ≤ y + h then w else 0) := by
  by_cases hy : y = c
  · subst hy
    simp [hh, hh.ne']
  · by_cases ht : y + h = c
    · subst ht
      simp [hh, hh.ne', hh.le]
    · have hiff : (y ≤ c ∧ c < y + h) ↔ (y < c ∧ c ≤ y + h) :=
        ⟨fun ⟨a, b⟩ => ⟨lt_of_le_of_ne a hy, b.le⟩, fun ⟨a, b⟩ => ⟨a.le, lt_of_le_of_ne b (Ne.symm ht)⟩⟩
      simp [hiff, hy, ht]

/-- Strictly between the bottom and the top of the main rectangle, the tiles whose bottom sides lie at a given height have the same total width as those whose top sides lie at that height. -/
theorem IsTiling.sum_bottom_eq_sum_top (h : IsTiling (Rect.main W H) tl) (hW : 0 ≤ W) {c : ℝ}
    (hc0 : 0 < c) (hcH : c < H) :
    ∑ e : Fin tl.length, (if (tl.get e).y = c then (tl.get e).w else 0) =
      ∑ e : Fin tl.length, (if (tl.get e).y + (tl.get e).h = c then (tl.get e).w else 0) := by
  have h1 := h.sum_above hW hc0.le hcH
  have h2 := h.sum_below hW hc0 hcH.le
  have h3 : ∑ e : Fin tl.length, ((if (tl.get e).y = c then (tl.get e).w else 0) -
      (if (tl.get e).y + (tl.get e).h = c then (tl.get e).w else 0)) = 0 := by
    rw [Finset.sum_congr rfl fun e _ => ite_level (h.get_bounds e).2.1, Finset.sum_sub_distrib, h1, h2, sub_self]
  rw [Finset.sum_sub_distrib] at h3
  linarith

/-- The tiles whose bottom sides lie on the bottom side of the main rectangle have its width in total. -/
theorem IsTiling.sum_bottom_zero (h : IsTiling (Rect.main W H) tl) (hW : 0 ≤ W) (hH : 0 < H) :
    ∑ e : Fin tl.length, (if (tl.get e).y = 0 then (tl.get e).w else 0) = W := by
  rw [← h.sum_above hW le_rfl hH]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hb := h.get_bounds e
  have hiff : (tl.get e).y = 0 ↔ ((tl.get e).y ≤ 0 ∧ 0 < (tl.get e).y + (tl.get e).h) :=
    ⟨fun a => ⟨a.le, by linarith⟩, fun a => le_antisymm a.1 hb.2.2.2.2.1⟩
  simp only [hiff]

/-- The tiles whose top sides lie on the top side of the main rectangle have its width in total. -/
theorem IsTiling.sum_top_height (h : IsTiling (Rect.main W H) tl) (hW : 0 ≤ W) (hH : 0 < H) :
    ∑ e : Fin tl.length, (if (tl.get e).y + (tl.get e).h = H then (tl.get e).w else 0) = W := by
  rw [← h.sum_below hW hH le_rfl]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hb := h.get_bounds e
  have hiff : (tl.get e).y + (tl.get e).h = H ↔ ((tl.get e).y < H ∧ H ≤ (tl.get e).y + (tl.get e).h) :=
    ⟨fun a => ⟨by linarith, a.ge⟩, fun a => le_antisymm hb.2.2.2.2.2 a.2⟩
  simp only [hiff]

end Rectiling
