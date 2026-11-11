-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Scaling

/-!
# Translation, refinement and juxtaposition of tilings

The image of a tiling under a translation, the replacement of a tile by a tiling of that tile, and the tilings obtained by placing two tilings side by side or one above the other.
-/

namespace Rectiling

namespace Rect

/-- The image under the translation by the vector `(a, b)`. -/
def translate (a b : ℝ) (r : Rect) : Rect :=
  ⟨r.x + a, r.y + b, r.w, r.h⟩

theorem mem_closed_translate {a b : ℝ} {r : Rect} {p : ℝ × ℝ} :
    p ∈ (r.translate a b).closed ↔ (p.1 - a, p.2 - b) ∈ r.closed := by
  simp only [mem_closed, translate]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_inner_translate {a b : ℝ} {r : Rect} {p : ℝ × ℝ} :
    p ∈ (r.translate a b).inner ↔ (p.1 - a, p.2 - b) ∈ r.inner := by
  simp only [mem_inner, translate]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- A rectangle contained in another has its interior contained in the interior of the other. -/
theorem inner_subset_of_closed_subset {s t : Rect} (h : s.closed ⊆ t.closed) :
    s.inner ⊆ t.inner := by
  rw [← interior_closed, ← interior_closed]
  exact interior_mono h

/-- A rectangle whose sides are those of a rectangle of proportion `x`, multiplied by a common factor, has proportion `x`. -/
theorem HasProportion.of_scaled {x c : ℝ} {r t : Rect} (hw : t.w = c * r.w) (hh : t.h = c * r.h)
    (h : r.HasProportion x) : t.HasProportion x := by
  rcases h with h | h
  · left
    rw [hw, hh, h]
    ring
  · right
    rw [hw, hh, h]
    ring

end Rect

theorem IsTiling.translate {R : Rect} {tiles : List Rect} (a b : ℝ) (h : IsTiling R tiles) :
    IsTiling (R.translate a b) (tiles.map (Rect.translate a b)) where
  nondegenerate t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact h.nondegenerate s hs
  cover := by
    ext p
    have hcov := h.cover
    rw [Set.ext_iff] at hcov
    have hp := hcov (p.1 - a, p.2 - b)
    simp only [Set.mem_iUnion, exists_prop] at hp
    simp only [Set.mem_iUnion, exists_prop, List.mem_map, exists_exists_and_eq_and,
      Rect.mem_closed_translate]
    exact hp
  disjoint := by
    rw [List.pairwise_map]
    refine h.disjoint.imp ?_
    intro s t hst
    rw [Set.disjoint_left] at hst ⊢
    intro p hps hpt
    exact hst (Rect.mem_inner_translate.mp hps) (Rect.mem_inner_translate.mp hpt)

theorem IsSimilarTiling.translate {x : ℝ} {R : Rect} {tiles : List Rect} (a b : ℝ)
    (h : IsSimilarTiling x R tiles) :
    IsSimilarTiling x (R.translate a b) (tiles.map (Rect.translate a b)) where
  toIsTiling := h.toIsTiling.translate a b
  one_le := h.one_le
  proportion t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact h.proportion s hs

/-- **Refinement.** Replacing the first tile of a tiling by a tiling of that tile gives a tiling. -/
theorem IsTiling.refine {R t : Rect} {rest sub : List Rect} (h : IsTiling R (t :: rest))
    (hs : IsTiling t sub) : IsTiling R (sub ++ rest) where
  nondegenerate u hu := by
    rcases List.mem_append.mp hu with hu | hu
    · exact hs.nondegenerate u hu
    · exact h.nondegenerate u (List.mem_cons_of_mem _ hu)
  cover := by
    rw [← h.cover]
    ext p
    have hcov := hs.cover
    rw [Set.ext_iff] at hcov
    have hp := hcov p
    simp only [Set.mem_iUnion, exists_prop] at hp
    simp only [Set.mem_iUnion, exists_prop, List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨u, hu | hu, hpu⟩
      · exact ⟨t, Or.inl rfl, hp.mp ⟨u, hu, hpu⟩⟩
      · exact ⟨u, Or.inr hu, hpu⟩
    · rintro ⟨u, hu | hu, hpu⟩
      · rw [hu] at hpu
        obtain ⟨v, hv, hpv⟩ := hp.mpr hpu
        exact ⟨v, Or.inl hv, hpv⟩
      · exact ⟨u, Or.inr hu, hpu⟩
  disjoint := by
    rw [List.pairwise_append]
    have hd := h.disjoint
    rw [List.pairwise_cons] at hd
    refine ⟨hs.disjoint, hd.2, ?_⟩
    intro a ha b hb
    exact Disjoint.mono_left (Rect.inner_subset_of_closed_subset (hs.subset ha)) (hd.1 b hb)

theorem IsSimilarTiling.refine {x : ℝ} {R t : Rect} {rest sub : List Rect}
    (h : IsSimilarTiling x R (t :: rest)) (hs : IsTiling t sub)
    (hp : ∀ u ∈ sub, u.HasProportion x) : IsSimilarTiling x R (sub ++ rest) where
  toIsTiling := h.toIsTiling.refine hs
  one_le := h.one_le
  proportion u hu := by
    rcases List.mem_append.mp hu with hu | hu
    · exact hp u hu
    · exact h.proportion u (List.mem_cons_of_mem _ hu)

/-- A rectangle with positive sides is tiled by itself. -/
theorem isTiling_singleton {r : Rect} (hr : r.Nondegenerate) : IsTiling r [r] where
  nondegenerate t ht := by
    rw [List.mem_singleton] at ht
    rw [ht]
    exact hr
  cover := by simp
  disjoint := List.pairwise_singleton _ _

/-- A rectangle is tiled by the two parts into which a vertical line cuts it. -/
theorem isTiling_hsplit {x y a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    IsTiling ⟨x, y, a + b, h⟩ [⟨x, y, a, h⟩, ⟨x + a, y, b, h⟩] where
  nondegenerate t ht := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨ha, hh⟩
    · exact ⟨hb, hh⟩
  cover := by
    ext p
    simp only [Set.mem_iUnion, exists_prop, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left, Rect.mem_closed]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total p.1 (x + a) with h5 | h5
      · left
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
      · right
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  disjoint := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    apply Rect.disjoint_inner_of_separated
    left
    exact le_refl _

/-- A rectangle is tiled by the two parts into which a horizontal line cuts it. -/
theorem isTiling_vsplit {x y w a b : ℝ} (hw : 0 < w) (ha : 0 < a) (hb : 0 < b) :
    IsTiling ⟨x, y, w, a + b⟩ [⟨x, y, w, a⟩, ⟨x, y + a, w, b⟩] where
  nondegenerate t ht := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨hw, ha⟩
    · exact ⟨hw, hb⟩
  cover := by
    ext p
    simp only [Set.mem_iUnion, exists_prop, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left, Rect.mem_closed]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total p.2 (y + a) with h5 | h5
      · left
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
      · right
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  disjoint := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    apply Rect.disjoint_inner_of_separated
    right
    right
    left
    exact le_refl _

/-- Tilings of two rectangles that share a vertical side form a tiling of their union. -/
theorem IsTiling.hcat {x y a b h : ℝ} {A B : List Rect} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hA : IsTiling ⟨x, y, a, h⟩ A) (hB : IsTiling ⟨x + a, y, b, h⟩ B) :
    IsTiling ⟨x, y, a + b, h⟩ (A ++ B) := by
  have h1 := ((isTiling_hsplit (x := x) (y := y) ha hb hh).refine hA).perm List.perm_append_comm
  exact (h1.refine hB).perm List.perm_append_comm

/-- Tilings of two rectangles that share a horizontal side form a tiling of their union. -/
theorem IsTiling.vcat {x y w a b : ℝ} {A B : List Rect} (hw : 0 < w) (ha : 0 < a) (hb : 0 < b)
    (hA : IsTiling ⟨x, y, w, a⟩ A) (hB : IsTiling ⟨x, y + a, w, b⟩ B) :
    IsTiling ⟨x, y, w, a + b⟩ (A ++ B) := by
  have h1 := ((isTiling_vsplit (x := x) (y := y) hw ha hb).refine hA).perm List.perm_append_comm
  exact (h1.refine hB).perm List.perm_append_comm

end Rectiling
