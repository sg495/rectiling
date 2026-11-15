-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.CrossSection
import Rectiling.NetworkPolynomial

/-!
# The network of the heights of a tiling

The network whose vertices are the heights of the horizontal sides of the tiles of a tiling of a rectangle and whose edges are the tiles, each from the height of its top side to the height of its bottom side.
The heights and the widths of the tiles form a flow, whose value is the width of the main rectangle, so that the height of the main rectangle over its width is the impedance of the network; and the proportion of a similar tiling of the unit square is a root of the polynomial of the network.
-/

namespace Rectiling

variable {W H : ℝ} {tl : List Rect}

open Classical in
/-- The heights of the top sides of the tiles, and zero. -/
noncomputable def levels (tl : List Rect) : Finset ℝ :=
  insert 0 (Finset.univ.image fun e : Fin tl.length => (tl.get e).y + (tl.get e).h)

theorem card_levels_le (tl : List Rect) : (levels tl).card ≤ tl.length + 1 := by
  classical
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_image_le.trans (by simp)))

theorem top_mem_levels (e : Fin tl.length) : (tl.get e).y + (tl.get e).h ∈ levels tl :=
  Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem (fun e : Fin tl.length => (tl.get e).y + (tl.get e).h) (Finset.mem_univ e))

theorem eq_zero_or_top_of_mem_levels {c : ℝ} (hc : c ∈ levels tl) :
    c = 0 ∨ ∃ e : Fin tl.length, (tl.get e).y + (tl.get e).h = c := by
  classical
  rcases Finset.mem_insert.mp hc with h | h
  · exact Or.inl h
  · obtain ⟨e, -, he⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨e, he⟩

open Classical in
/-- The network of the heights of a list of tiles, for a main rectangle of height `H`: its vertices are the heights, its poles are `H` and zero, and each tile is an edge from the height of its top side to that of its bottom side. -/
noncomputable def heightNetwork (H : ℝ) (tl : List Rect) : Network {c : ℝ // c ∈ levels tl} (Fin tl.length) where
  tail e := ⟨(tl.get e).y + (tl.get e).h, top_mem_levels e⟩
  head e := if hm : (tl.get e).y ∈ levels tl then ⟨(tl.get e).y, hm⟩ else ⟨0, Finset.mem_insert_self _ _⟩
  source := if hm : H ∈ levels tl then ⟨H, hm⟩ else ⟨0, Finset.mem_insert_self _ _⟩
  sink := ⟨0, Finset.mem_insert_self _ _⟩

namespace IsTiling

/-- A positive height that is the height of the main rectangle or of the bottom side of a tile is the height of the top side of a tile. -/
theorem exists_top_eq (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) {c : ℝ} (hc0 : 0 < c)
    (hc : c = H ∨ ∃ e : Fin tl.length, (tl.get e).y = c) :
    ∃ e : Fin tl.length, (tl.get e).y + (tl.get e).h = c := by
  by_contra hno
  have hz : ∑ e : Fin tl.length, (if (tl.get e).y + (tl.get e).h = c then (tl.get e).w else 0) = 0 :=
    Finset.sum_eq_zero fun e _ => ite_eq_right_iff.mpr fun he => absurd ⟨e, he⟩ hno
  rcases hc with rfl | ⟨e, he⟩
  · rw [h.sum_top_height hW.le hH] at hz
    exact hW.ne' hz
  · have hb := h.get_bounds e
    have hcH : c < H := by linarith
    rw [← h.sum_bottom_eq_sum_top hW.le hc0 hcH] at hz
    have hle := Finset.single_le_sum
      (f := fun e : Fin tl.length => if (tl.get e).y = c then (tl.get e).w else 0)
      (fun i _ => by
        have := (h.get_bounds i).1
        split_ifs
        · exact this.le
        · exact le_rfl) (Finset.mem_univ e)
    simp only [he, ite_true] at hle
    linarith

theorem bottom_mem_levels (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) (e : Fin tl.length) :
    (tl.get e).y ∈ levels tl := by
  have hb := h.get_bounds e
  rcases hb.2.2.2.2.1.eq_or_lt with h0 | h0
  · rw [← h0]
    exact Finset.mem_insert_self _ _
  · obtain ⟨e', he'⟩ := h.exists_top_eq hW hH h0 (Or.inr ⟨e, rfl⟩)
    rw [← he']
    exact top_mem_levels e'

theorem height_mem_levels (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) : H ∈ levels tl := by
  obtain ⟨e, he⟩ := h.exists_top_eq hW hH hH (Or.inl rfl)
  rw [← he]
  exact top_mem_levels e

theorem head_val (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) (e : Fin tl.length) :
    ((heightNetwork H tl).head e).1 = (tl.get e).y := by
  simp only [heightNetwork, h.bottom_mem_levels hW hH e, ↓reduceDIte]

theorem source_val (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    ((heightNetwork H tl).source).1 = H := by
  simp only [heightNetwork, h.height_mem_levels hW hH, ↓reduceDIte]

/-- The net current that the widths of the tiles give at a height. -/
theorem heightNetwork_div (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H)
    (v : {c : ℝ // c ∈ levels tl}) :
    (heightNetwork H tl).div (fun e => (tl.get e).w) v =
      ∑ e : Fin tl.length, (if (tl.get e).y + (tl.get e).h = v.1 then (tl.get e).w else 0) -
        ∑ e : Fin tl.length, (if (tl.get e).y = v.1 then (tl.get e).w else 0) := by
  simp only [Network.div, Finset.sum_sub_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun e _ => ?_
  · have hiff : (heightNetwork H tl).tail e = v ↔ (tl.get e).y + (tl.get e).h = v.1 := Subtype.ext_iff
    simp only [hiff]
  · have hiff : (heightNetwork H tl).head e = v ↔ (tl.get e).y = v.1 := by
      rw [Subtype.ext_iff, h.head_val hW hH]
    simp only [hiff]

/-- The heights of the sides and the widths of the tiles form a flow of the network of the heights, whose value is the width of the main rectangle, for the resistances given by the height of each tile over its width. -/
theorem heightNetwork_isFlow (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    (heightNetwork H tl).IsFlow (fun e => (tl.get e).h / (tl.get e).w) W (fun v => v.1)
      (fun e => (tl.get e).w) where
  ohm e := by
    rw [h.head_val hW hH, div_mul_cancel₀ _ (h.get_bounds e).1.ne']
    exact add_sub_cancel_left _ _
  kirchhoff v := by
    rw [h.heightNetwork_div hW hH]
    have hs : v = (heightNetwork H tl).source ↔ v.1 = H := by rw [Subtype.ext_iff, h.source_val hW hH]
    have ht : v = (heightNetwork H tl).sink ↔ v.1 = 0 := Subtype.ext_iff
    simp only [hs, ht]
    obtain ⟨c, hc⟩ := v
    simp only
    by_cases h0 : c = 0
    · subst h0
      rw [h.sum_bottom_zero hW.le hH, Finset.sum_eq_zero fun e _ => ite_eq_right_iff.mpr fun he => ?_]
      · simp [hH.ne]
      · have hb := h.get_bounds e
        linarith
    · have hc0 : 0 < c := by
        rcases eq_zero_or_top_of_mem_levels hc with h1 | ⟨e, he⟩
        · exact absurd h1 h0
        · have hb := h.get_bounds e
          linarith
      by_cases h1 : c = H
      · subst h1
        rw [h.sum_top_height hW.le hH, Finset.sum_eq_zero fun e _ => ite_eq_right_iff.mpr fun he => ?_]
        · simp [h0]
        · have hb := h.get_bounds e
          linarith
      · have hcH : c < H := by
          rcases eq_zero_or_top_of_mem_levels hc with h2 | ⟨e, he⟩
          · exact absurd h2 h0
          · have hb := h.get_bounds e
            exact lt_of_le_of_ne (by linarith) h1
        rw [h.sum_bottom_eq_sum_top hW.le hc0 hcH]
        simp [h0, h1]

/-- The network of the heights of a tiling has distinct poles, no loop, and is connected. -/
theorem heightNetwork_proper (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    (heightNetwork H tl).Proper where
  source_ne_sink he := by
    have h1 := congrArg Subtype.val he
    rw [h.source_val hW hH] at h1
    exact hH.ne' h1
  loopless e he := by
    have h1 := congrArg Subtype.val he
    rw [h.head_val hW hH] at h1
    have hb := h.get_bounds e
    have h2 : (tl.get e).y + (tl.get e).h = (tl.get e).y := h1
    linarith
  connected v := by
    refine WellFoundedLT.induction
      (motive := fun v => Relation.ReflTransGen (heightNetwork H tl).Adj v (heightNetwork H tl).sink) v ?_
    rintro ⟨c, hc⟩ ih
    rcases eq_zero_or_top_of_mem_levels hc with h0 | ⟨e, he⟩
    · subst h0
      exact Relation.ReflTransGen.refl
    · refine Relation.ReflTransGen.head ⟨e, Or.inl ⟨Subtype.ext he, rfl⟩⟩ (ih _ ?_)
      have hb := h.get_bounds e
      have h1 := h.head_val hW hH e
      rw [← Subtype.coe_lt_coe, h1]
      simp only
      linarith

/-- The height of the main rectangle over its width is the impedance of the network of the heights of a tiling, for the resistances given by the height of each tile over its width. -/
theorem impedance_heightNetwork (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    (heightNetwork H tl).impedance (fun e => (tl.get e).h / (tl.get e).w) = H / W := by
  rw [← (h.heightNetwork_isFlow hW hH).impedance_eq (h.heightNetwork_proper hW hH)
    (fun e => div_pos (h.get_bounds e).2.1 (h.get_bounds e).1) hW.ne', h.source_val hW hH]
  exact congrArg (· / W) (sub_zero H)

end IsTiling

open Classical in
/-- The orientation vector of a list of tiles for the proportion `x`: a tile is marked when its height is `x` times its width. -/
noncomputable def tallVector (x : ℝ) (tl : List Rect) (e : Fin tl.length) : Bool :=
  decide ((tl.get e).h = x * (tl.get e).w)

/-- The resistances of the tiles of a similar tiling of proportion `x` are `x` for the marked tiles and `1 / x` for the others. -/
theorem IsSimilarTiling.resistance_eq {x : ℝ} {R : Rect} (h : IsSimilarTiling x R tl) (e : Fin tl.length) :
    (tl.get e).h / (tl.get e).w = if tallVector x tl e then x else x⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le one_pos h.one_le
  obtain ⟨hw, hh⟩ := h.nondegenerate _ (List.get_mem tl e)
  by_cases ht : (tl.get e).h = x * (tl.get e).w
  · simp only [tallVector, ht, decide_true, ↓reduceIte]
    rw [mul_div_assoc, div_self hw.ne', mul_one]
  · have hwide : (tl.get e).w = x * (tl.get e).h := (h.proportion _ (List.get_mem tl e)).resolve_right ht
    simp only [tallVector, ht, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [div_eq_iff hw.ne', hwide, inv_mul_cancel_left₀ hx.ne']

/-- The proportion of a similar tiling of the unit square is a root of the polynomial of the network of its heights with its orientation vector. -/
theorem IsSimilarTiling.aeval_pairPoly {x : ℝ} (h : IsSimilarTiling x (Rect.main 1 1) tl) :
    Polynomial.aeval x ((heightNetwork 1 tl).pairPoly (tallVector x tl)) = 0 := by
  have hx : 0 < x := lt_of_lt_of_le one_pos h.one_le
  have hf := h.toIsTiling.heightNetwork_isFlow one_pos one_pos
  rw [funext h.resistance_eq] at hf
  refine hf.aeval_pairPoly (h.toIsTiling.heightNetwork_proper one_pos one_pos).source_ne_sink hx one_ne_zero ?_
  rw [h.toIsTiling.source_val one_pos one_pos]
  exact sub_zero 1

end Rectiling
