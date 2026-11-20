-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.TilingMap
import Rectiling.MapNetwork

/-!
# The flow of a tiling on its map

The network of the map of a tiling has the vertices of the map as its vertices and the tiles as its edges, each from the vertex of its top end to the vertex of its bottom end.
The heights of the vertices and the widths of the tiles form a flow, whose value is the width of the main rectangle: the law of Kirchhoff at a vertex is a telescoping sum around its cycle of the rotation.
Hence the proportion of a similar tiling of the unit square is a root of the polynomial of this network.
-/

namespace Rectiling

open Classical

variable {W H : ℝ} {tl : List Rect} {M : CMap (Dart tl.length)}

/-- The network of a map on the darts of a tiling: each tile is an edge from the vertex of its top end to the vertex of its bottom end, and the poles are the vertices of the two ends of the additional edge. -/
def tilingNet (M : CMap (Dart tl.length)) : Network M.Vertex (Fin tl.length) where
  tail e := M.vertex (some e, true)
  head e := M.vertex (some e, false)
  source := M.vertex (none, true)
  sink := M.vertex (none, false)

namespace IsTilingMap

/-- The darts of a vertex lie at the same height. -/
theorem height_eq (hM : IsTilingMap W H tl M) {a b : Dart tl.length} (hab : M.σ.SameCycle a b) :
    dartHeight H tl a = dartHeight H tl b :=
  sameCycle_induction hab (fun d => dartHeight H tl a = dartHeight H tl d) rfl fun d hd => by
    rw [hM.rotation.height]
    exact hd

/-- The height of a vertex. -/
def vertexHeight (hM : IsTilingMap W H tl M) : M.Vertex → ℝ :=
  Quotient.lift (dartHeight H tl) fun _ _ hab => hM.height_eq hab

theorem vertexHeight_vertex (hM : IsTilingMap W H tl M) (d : Dart tl.length) :
    hM.vertexHeight (M.vertex d) = dartHeight H tl d :=
  rfl

/-- Around a vertex, the differences between the abscissas at which the darts stop and start add up to zero. -/
theorem sum_stop_sub_start (hM : IsTilingMap W H tl M) (v : M.Vertex) :
    ∑ d : Dart tl.length, (if M.vertex d = v then dartStop W tl d - dartStart W tl d else 0) = 0 := by
  have h1 : ∑ d : Dart tl.length, (if M.vertex d = v then dartStop W tl d else 0) =
      ∑ d : Dart tl.length, (if M.vertex d = v then dartStart W tl d else 0) := by
    rw [← Equiv.sum_comp M.σ fun d => if M.vertex d = v then dartStart W tl d else 0]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [M.vertex_σ, hM.rotation.start]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
  refine Eq.trans (Finset.sum_congr rfl fun d _ => ?_) h1
  split_ifs <;> ring

/-- The widths of the tiles satisfy the law of Kirchhoff at every vertex, with the width of the main rectangle as the value. -/
theorem tilingNet_div (hM : IsTilingMap W H tl M) (v : M.Vertex) :
    (tilingNet M).div (fun e => (tl.get e).w) v =
      W * ((if v = (tilingNet M).source then 1 else 0) - (if v = (tilingNet M).sink then 1 else 0)) := by
  have h0 := hM.sum_stop_sub_start v
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool, dartStop, dartStart] at h0
  have g1 : (if M.vertex (none, true) = v then 0 - W else 0) =
      -W * (if v = (tilingNet M).source then 1 else 0) := by
    by_cases a : M.vertex (none, true) = v
    · subst a
      simp [tilingNet]
    · have a' : ¬v = (tilingNet M).source := fun hv => a hv.symm
      simp [a, a']
  have g2 : (if M.vertex (none, false) = v then W - 0 else 0) =
      W * (if v = (tilingNet M).sink then 1 else 0) := by
    by_cases a : M.vertex (none, false) = v
    · subst a
      simp [tilingNet]
    · have a' : ¬v = (tilingNet M).sink := fun hv => a hv.symm
      simp [a, a']
  have h1 : ∀ e : Fin tl.length,
      ((if M.vertex (some e, true) = v then (tl.get e).x + (tl.get e).w - (tl.get e).x else 0) +
        if M.vertex (some e, false) = v then (tl.get e).x - ((tl.get e).x + (tl.get e).w) else 0) =
      (if M.vertex (some e, true) = v then (tl.get e).w else 0) -
        if M.vertex (some e, false) = v then (tl.get e).w else 0 := by
    intro e
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun e _ => h1 e, g1, g2] at h0
  have g3 : (tilingNet M).div (fun e => (tl.get e).w) v =
      ∑ e : Fin tl.length, ((if M.vertex (some e, true) = v then (tl.get e).w else 0) -
        if M.vertex (some e, false) = v then (tl.get e).w else 0) := rfl
  rw [g3]
  linarith

/-- The heights of the vertices and the widths of the tiles form a flow of the network of the map of a tiling, whose value is the width of the main rectangle. -/
theorem tilingNet_isFlow (hM : IsTilingMap W H tl M) (hw : ∀ e : Fin tl.length, (tl.get e).w ≠ 0) :
    (tilingNet M).IsFlow (fun e => (tl.get e).h / (tl.get e).w) W hM.vertexHeight fun e => (tl.get e).w where
  ohm e := by
    rw [div_mul_cancel₀ _ (hw e)]
    change (tl.get e).y + (tl.get e).h - (tl.get e).y = (tl.get e).h
    ring
  kirchhoff := hM.tilingNet_div

/-- The poles of the network of the map of a tiling are distinct. -/
theorem source_ne_sink (hM : IsTilingMap W H tl M) (hH : 0 < H) :
    (tilingNet M).source ≠ (tilingNet M).sink := fun he =>
  hH.ne' (hM.height_eq (M.vertex_eq_iff.mp he))

end IsTilingMap

/-- The orientation vector of a list of tiles for the proportion `x` in which a tile is marked when its width is not `x` times its height. -/
noncomputable def narrowVector (x : ℝ) (tl : List Rect) (e : Fin tl.length) : Bool :=
  decide ¬(tl.get e).w = x * (tl.get e).h

/-- The resistances of the tiles of a similar tiling of proportion `x` are `x` for the marked tiles and `1 / x` for the others. -/
theorem IsSimilarTiling.resistance_eq_narrow {x : ℝ} {R : Rect} (h : IsSimilarTiling x R tl) (e : Fin tl.length) :
    (tl.get e).h / (tl.get e).w = if narrowVector x tl e then x else x⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le one_pos h.one_le
  obtain ⟨hw, hh⟩ := h.nondegenerate _ (List.get_mem tl e)
  by_cases hwide : (tl.get e).w = x * (tl.get e).h
  · simp only [narrowVector, hwide, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [div_eq_iff (by positivity), inv_mul_cancel_left₀ hx.ne']
  · have ht : (tl.get e).h = x * (tl.get e).w := (h.proportion _ (List.get_mem tl e)).resolve_left hwide
    simp only [narrowVector, hwide, not_false_eq_true, decide_true, ↓reduceIte]
    rw [ht, mul_div_assoc, div_self hw.ne', mul_one]

/-- The proportion of a similar tiling of the unit square is a root of the polynomial of the network of its map, for the orientation vector that marks the tiles that are not wide. -/
theorem IsSimilarTiling.aeval_tilingNet {x : ℝ} (h : IsSimilarTiling x (Rect.main 1 1) tl)
    (hM : IsTilingMap 1 1 tl M) : Polynomial.aeval x ((tilingNet M).pairPoly (narrowVector x tl)) = 0 := by
  have hx : 0 < x := lt_of_lt_of_le one_pos h.one_le
  have hf := hM.tilingNet_isFlow fun e => (h.nondegenerate _ (List.get_mem tl e)).1.ne'
  rw [funext h.resistance_eq_narrow] at hf
  refine hf.aeval_pairPoly (hM.source_ne_sink one_pos) hx one_ne_zero ?_
  change (1 : ℝ) - 0 = 1
  exact sub_zero 1

end Rectiling
