-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Extension

/-!
# Crossings of a tiling

A crossing of a tiling is a point that is a corner of four tiles.
Such a point is the top-left corner of one tile, which lies to its lower right, and the bottom-right corner of another, which lies to its upper left, and these two tiles suffice to recognise it.
The order in which two tiles occur in a list is expressed by the sublist relation.
-/

namespace Rectiling

open scoped List

/-! ### The order of two elements of a list -/

theorem pair_sublist_cons {α : Type} {a b c : α} {l : List α} :
    [a, b] <+ c :: l ↔ [a, b] <+ l ∨ (a = c ∧ b ∈ l) := by
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, hr, h⟩)
    · exact Or.inl h
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact Or.inr ⟨rfl, List.singleton_sublist.mp h⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨[b], rfl, List.singleton_sublist.mpr h⟩

/-- In a list without repetitions, two elements do not occur in both orders. -/
theorem pair_sublist_asymm {α : Type} {a b : α} :
    ∀ {l : List α}, l.Nodup → [a, b] <+ l → [b, a] <+ l → False
  | [], _, h, _ => by simp at h
  | c :: l, hl, h1, h2 => by
    rw [pair_sublist_cons] at h1 h2
    rw [List.nodup_cons] at hl
    rcases h1 with h1 | ⟨rfl, hb⟩
    · rcases h2 with h2 | ⟨rfl, -⟩
      · exact pair_sublist_asymm hl.2 h1 h2
      · exact hl.1 (h1.subset (by simp))
    · rcases h2 with h2 | ⟨rfl, -⟩
      · exact hl.1 (h2.subset (by simp))
      · exact hl.1 hb

/-- Two distinct elements of a list occur in one order or the other. -/
theorem pair_sublist_total {α : Type} {a b : α} (hab : a ≠ b) :
    ∀ {l : List α}, a ∈ l → b ∈ l → [a, b] <+ l ∨ [b, a] <+ l
  | [], h, _ => by simp at h
  | c :: l, ha, hb => by
    rw [pair_sublist_cons, pair_sublist_cons]
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · exact Or.inl (Or.inr ⟨ha', hb'⟩)
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact Or.inr (Or.inr ⟨hb', ha'⟩)
      · rcases pair_sublist_total hab ha' hb' with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)

/-! ### Tiles with a common corner -/

variable {W H : ℝ} {tl : List Rect}

/-- Two tiles of a tiling with a common corner, on the same side of each, are equal. -/
theorem IsTiling.eq_of_corner {R : Rect} (h : IsTiling R tl) {S T : Rect} (hS : S ∈ tl)
    (hT : T ∈ tl) (hx : S.x = T.x ∨ S.x + S.w = T.x + T.w)
    (hy : S.y = T.y ∨ S.y + S.h = T.y + T.h) : S = T := by
  have hSn := h.nondegenerate S hS
  have hTn := h.nondegenerate T hT
  apply h.eq_of_not_disjoint hS hT
  apply Rect.not_disjoint_inner_of_overlap
  · rw [max_lt_iff, lt_min_iff, lt_min_iff]
    rcases hx with hx | hx <;>
      exact ⟨⟨by linarith [hSn.1, hTn.1], by linarith [hSn.1, hTn.1]⟩,
        ⟨by linarith [hSn.1, hTn.1], by linarith [hSn.1, hTn.1]⟩⟩
  · rw [max_lt_iff, lt_min_iff, lt_min_iff]
    rcases hy with hy | hy <;>
      exact ⟨⟨by linarith [hSn.2, hTn.2], by linarith [hSn.2, hTn.2]⟩,
        ⟨by linarith [hSn.2, hTn.2], by linarith [hSn.2, hTn.2]⟩⟩

/-- The tiles of a tiling are distinct. -/
theorem IsTiling.nodup {R : Rect} (h : IsTiling R tl) : tl.Nodup := by
  refine h.disjoint.imp_of_mem ?_
  rintro a b ha - hd rfl
  exact Rect.not_disjoint_inner_self (h.nondegenerate a ha) hd

/-- The tiles of a tiling of the main rectangle lie between its sides. -/
theorem IsTiling.bounds (h : IsTiling (Rect.main W H) tl) {T : Rect} (hT : T ∈ tl) :
    0 ≤ T.x ∧ T.x + T.w ≤ W ∧ 0 ≤ T.y ∧ T.y + T.h ≤ H := by
  have hnd := h.nondegenerate T hT
  have h1 := h.subset hT (a := (T.x, T.y)) (by
    rw [Rect.mem_closed]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith [hnd.1, hnd.2])
  have h2 := h.subset hT (a := (T.x + T.w, T.y + T.h)) (by
    rw [Rect.mem_closed]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith [hnd.1, hnd.2])
  rw [Rect.mem_closed] at h1 h2
  simp only [Rect.main, zero_add] at h1 h2
  exact ⟨h1.1, h2.2.1, h1.2.2.1, h2.2.2.2⟩

/-- A tile of a tiling that contains all points slightly below and to the left of a given point. -/
theorem IsTiling.exists_tile_below_left (h : IsTiling (Rect.main W H) tl) {cx cy : ℝ}
    (hx0 : 0 < cx) (hx1 : cx ≤ W) (hy0 : 0 < cy) (hy1 : cy ≤ H) :
    ∃ T ∈ tl, T.x < cx ∧ cx ≤ T.x + T.w ∧ T.y < cy ∧ cy ≤ T.y + T.h := by
  obtain ⟨ε1, a1, a2, a3⟩ := exists_gap (tl.map fun T => T.x + T.w) cx cx hx0
  obtain ⟨ε2, b1, b2, b3⟩ := exists_gap (tl.map fun T => T.y + T.h) cy cy hy0
  have hp : ((cx - ε1, cy - ε2) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
    rw [Rect.mem_closed]
    simp only [Rect.main]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨T, hT, hpT⟩ := h.exists_mem hp
  rw [Rect.mem_closed] at hpT
  simp only at hpT
  exact ⟨T, hT, by linarith,
    (a3 (T.x + T.w) (List.mem_map_of_mem (f := fun T : Rect => T.x + T.w) hT)).2 hpT.2.1,
    by linarith,
    (b3 (T.y + T.h) (List.mem_map_of_mem (f := fun T : Rect => T.y + T.h) hT)).2 hpT.2.2.2⟩

/-! ### Crossings -/

/-- The point is the top-left corner of the rectangle, which lies to its lower right. -/
def Rect.LowerRightOf (T : Rect) (q : ℝ × ℝ) : Prop :=
  T.x = q.1 ∧ T.y + T.h = q.2

/-- The point is the bottom-right corner of the rectangle, which lies to its upper left. -/
def Rect.UpperLeftOf (T : Rect) (q : ℝ × ℝ) : Prop :=
  T.x + T.w = q.1 ∧ T.y = q.2

/-- The point is a corner of the rectangle. -/
def Rect.HasCorner (T : Rect) (q : ℝ × ℝ) : Prop :=
  (T.x = q.1 ∨ T.x + T.w = q.1) ∧ (T.y = q.2 ∨ T.y + T.h = q.2)

/-- A crossing: a point that is a corner of four tiles. -/
def IsCrossing (tl : List Rect) (q : ℝ × ℝ) : Prop :=
  ∃ l : List Rect, l.Nodup ∧ l.length = 4 ∧ ∀ T ∈ l, T ∈ tl ∧ T.HasCorner q

open Classical in
/-- A point is a crossing of a tiling exactly if it is the top-left corner of a tile and the bottom-right corner of another. -/
theorem isCrossing_iff (h : IsTiling (Rect.main W H) tl) {q : ℝ × ℝ} :
    IsCrossing tl q ↔ ∃ U ∈ tl, ∃ V ∈ tl, U.LowerRightOf q ∧ V.UpperLeftOf q := by
  constructor
  · rintro ⟨l, hnd, hlen, hl⟩
    let kind : Rect → Bool × Bool := fun T => (decide (T.x = q.1), decide (T.y = q.2))
    have hinj : ∀ S ∈ l, ∀ T ∈ l, kind S = kind T → S = T := by
      intro S hS T hT hk
      simp only [kind, Prod.mk.injEq, decide_eq_decide] at hk
      obtain ⟨hSx, hSy⟩ := (hl S hS).2
      obtain ⟨hTx, hTy⟩ := (hl T hT).2
      refine h.eq_of_corner (hl S hS).1 (hl T hT).1 ?_ ?_
      · by_cases hc : S.x = q.1
        · exact Or.inl (hc.trans (hk.1.mp hc).symm)
        · exact Or.inr ((hSx.resolve_left hc).trans
            (hTx.resolve_left fun hT' => hc (hk.1.mpr hT')).symm)
      · by_cases hc : S.y = q.2
        · exact Or.inl (hc.trans (hk.2.mp hc).symm)
        · exact Or.inr ((hSy.resolve_left hc).trans
            (hTy.resolve_left fun hT' => hc (hk.2.mpr hT')).symm)
    have hmap : (l.map kind).Nodup := hnd.map_on hinj
    have hall : ∀ b : Bool × Bool, b ∈ l.map kind := by
      intro b
      have hcard : (l.map kind).toFinset.card = Fintype.card (Bool × Bool) := by
        rw [List.toFinset_card_of_nodup hmap, List.length_map, hlen]
        rfl
      have := Finset.eq_univ_of_card _ hcard
      exact List.mem_toFinset.mp (this ▸ Finset.mem_univ b)
    obtain ⟨U, hU, hkU⟩ := List.mem_map.mp (hall (true, false))
    obtain ⟨V, hV, hkV⟩ := List.mem_map.mp (hall (false, true))
    simp only [kind, Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not] at hkU hkV
    exact ⟨U, (hl U hU).1, V, (hl V hV).1, ⟨hkU.1, (hl U hU).2.2.resolve_left hkU.2⟩,
      ⟨(hl V hV).2.1.resolve_left hkV.1, hkV.2⟩⟩
  · rintro ⟨U, hU, V, hV, ⟨hUx, hUy⟩, ⟨hVx, hVy⟩⟩
    obtain ⟨hUw, hUh⟩ := h.nondegenerate U hU
    obtain ⟨hVw, hVh⟩ := h.nondegenerate V hV
    obtain ⟨u1, u2, u3, u4⟩ := h.bounds hU
    obtain ⟨v1, v2, v3, v4⟩ := h.bounds hV
    obtain ⟨A, hA, a1, a2, a3, a4⟩ := h.exists_tile_above_right (cx := q.1) (cy := q.2)
      (by linarith) (by linarith) (by linarith) (by linarith)
    obtain ⟨B, hB, b1, b2, b3, b4⟩ := h.exists_tile_below_left (cx := q.1) (cy := q.2)
      (by linarith) (by linarith) (by linarith) (by linarith)
    obtain ⟨hAw, hAh⟩ := h.nondegenerate A hA
    obtain ⟨hBw, hBh⟩ := h.nondegenerate B hB
    have hAy : A.y = q.2 := by
      refine le_antisymm a3 ?_
      by_contra hc
      have hAU : A = U := by
        apply h.eq_of_not_disjoint hA hU
        apply Rect.not_disjoint_inner_of_overlap
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      rw [hAU] at a4
      linarith
    have hAx : A.x = q.1 := by
      refine le_antisymm a1 ?_
      by_contra hc
      have hAV : A = V := by
        apply h.eq_of_not_disjoint hA hV
        apply Rect.not_disjoint_inner_of_overlap
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      rw [hAV] at a2
      linarith
    have hBx : B.x + B.w = q.1 := by
      refine le_antisymm ?_ b2
      by_contra hc
      have hBU : B = U := by
        apply h.eq_of_not_disjoint hB hU
        apply Rect.not_disjoint_inner_of_overlap
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      rw [hBU] at b1
      linarith
    have hBy : B.y + B.h = q.2 := by
      refine le_antisymm ?_ b4
      by_contra hc
      have hBV : B = V := by
        apply h.eq_of_not_disjoint hB hV
        apply Rect.not_disjoint_inner_of_overlap
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      rw [hBV] at b3
      linarith
    refine ⟨[A, B, U, V], ?_, rfl, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
        List.nodup_nil, and_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
    · intro T hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · exact ⟨hA, Or.inl hAx, Or.inl hAy⟩
      · exact ⟨hB, Or.inr hBx, Or.inr hBy⟩
      · exact ⟨hU, Or.inl hUx, Or.inr hUy⟩
      · exact ⟨hV, Or.inr hVx, Or.inl hVy⟩

/-- The crossings of a tiling are finitely many. -/
theorem finite_crossings (h : IsTiling (Rect.main W H) tl) : {q | IsCrossing tl q}.Finite := by
  refine ((List.finite_toSet tl).image fun U : Rect => (U.x, U.y + U.h)).subset ?_
  intro q hq
  obtain ⟨U, hU, -, -, ⟨hUx, hUy⟩, -⟩ := (isCrossing_iff h).mp hq
  exact ⟨U, hU, Prod.ext hUx hUy⟩

end Rectiling
