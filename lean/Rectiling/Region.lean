-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Layout

/-!
# The effect of a placement on the region to be filled

A tile of positive size that fits its tier, in a staircase with positive floors and walls, lies in the region to be filled, and the region after the placement is the region before it with the tile removed.
-/

namespace Rectiling

/-- Geometric hypotheses on a placement of a tile of width `w` and height `h` at the tier `g`, with the tiers `Gpre` before it and `Gpost` after it. -/
structure StepHyp (W : ℝ) (Gpre : List GTier) (g : GTier) (Gpost : List GTier) (fit : Fit)
    (w h : ℝ) : Prop where
  pre_above : ∀ g' ∈ Gpre, g.ay + g.wall ≤ g'.ay
  post_right : ∀ g' ∈ Gpost, g.ax + g.floor ≤ g'.ax ∧ g'.ay + g'.wall ≤ g.ay ∧ 0 ≤ g'.wall
  head : ∀ q ∈ Gpost.head?, q.ax = g.ax + g.floor ∧ q.ay + q.wall = g.ay
  last : Gpost = [] → g.ax + g.floor = W
  le_W : g.ax + g.floor ≤ W
  w_pos : 0 < w
  h_pos : 0 < h
  narrow : if fit.narrow then w < g.floor else w = g.floor
  low : if fit.low then h < g.wall else h = g.wall

/-- The geometric hypotheses hold for a staircase with positive floors and walls. -/
theorem stepHyp_of_positive {W H : ℝ} {pre post : List (Tier ℝ)} {t : Tier ℝ}
    (hs : Positive (pre ++ t :: post)) {fit : Fit} {w h : ℝ} (hw : 0 < w) (hh : 0 < h)
    (hn : if fit.narrow then w < t.floor else w = t.floor)
    (hl : if fit.low then h < t.wall else h = t.wall) :
    StepHyp W (geom (W - (t.floor + sumFloor post)) H pre)
      ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale, t.started⟩
      (geom W (H - sumWall pre - t.wall) post) fit w h := by
  have hpre : Positive pre := fun u hu => hs u (by simp [hu])
  have hpost : Positive post := fun u hu => hs u (by simp [hu])
  have hsum := hpost.sumFloor_nonneg
  refine ⟨?_, ?_, ?_, ?_, ?_, hw, hh, hn, hl⟩
  · intro g' hg'
    have := (geom_bounds hpre g' hg').2.2.1
    simp only
    linarith
  · intro g' hg'
    obtain ⟨b1, _, _, b4, _, b6⟩ := geom_bounds hpost g' hg'
    simp only
    exact ⟨by linarith, b4, b6.le⟩
  · intro q hq
    cases post with
    | nil => simp [geom] at hq
    | cons u l =>
      simp only [geom, List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      simp only [sumFloor_cons]
      constructor <;> ring
  · intro hnil
    cases post with
    | nil => simp
    | cons u l => simp [geom] at hnil
  · simp only
    linarith

theorem unfilled_gpreAfter (W : ℝ) (fit : Fit) (w : ℝ) (G : List GTier) :
    unfilled W (gpreAfter fit w G) = unfilled W G := by
  apply unfilled_congr
  unfold gpreAfter
  split
  · simp [Function.comp_def]
  · rcases List.eq_nil_or_concat G with rfl | ⟨G', a, rfl⟩ <;> simp [Function.comp_def]

theorem map_ax_gpostAfter (fit : Fit) (h : ℝ) (G : List GTier) :
    (gpostAfter fit h G).map GTier.ax = G.map GTier.ax := by
  unfold gpostAfter
  split
  · rfl
  · cases G <;> simp [onHead]

section Step

variable {W : ℝ} {Gpre Gpost : List GTier} {g : GTier} {fit : Fit} {w h : ℝ}

/-- The tile lies in the region to be filled. -/
theorem StepHyp.tile_subset (hyp : StepHyp W Gpre g Gpost fit w h) :
    (⟨g.ax, g.ay, w, h⟩ : Rect).closed ⊆ unfilled W (Gpre ++ g :: Gpost) := by
  intro p hp
  rw [Rect.mem_closed] at hp
  simp only at hp
  rw [mem_unfilled_append, mem_unfilled_cons]
  refine Or.inr (Or.inl ?_)
  have hn : w ≤ g.floor := by
    have := hyp.narrow
    split at this <;> linarith
  have hl : h ≤ g.wall := by
    have := hyp.low
    split at this <;> linarith
  have := hyp.le_W
  exact ⟨hp.1, by linarith [hp.2.1], hp.2.2.1, by linarith [hp.2.2.2]⟩

/-- The region to be filled after the placement is part of the region before it. -/
theorem StepHyp.unfilled_subset (hyp : StepHyp W Gpre g Gpost fit w h) :
    unfilled W (gpreAfter fit w Gpre ++ gmidAfter fit g w h ++ gpostAfter fit h Gpost) ⊆
      unfilled W (Gpre ++ g :: Gpost) := by
  intro p hp
  have hn := hyp.narrow
  have hl := hyp.low
  have hw := hyp.w_pos
  have hh := hyp.h_pos
  rw [mem_unfilled_append, mem_unfilled_append, unfilled_gpreAfter] at hp
  rw [mem_unfilled_append, mem_unfilled_cons]
  rcases hp with (hp | hp) | hp
  · exact Or.inl hp
  · refine Or.inr (Or.inl ?_)
    cases fit <;> simp only [gmidAfter, mem_unfilled_cons, unfilled_nil, Set.mem_empty_iff_false,
      or_false, GTier.Mem, Fit.narrow, Fit.low, ite_true, Bool.false_eq_true, ite_false] at hp hn hl
    · rcases hp with hp | hp <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
        linarith [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
  · unfold gpostAfter at hp
    split at hp
    · exact Or.inr (Or.inr hp)
    · rename_i hnar
      have hwf : w = g.floor := by simpa [hnar] using hn
      have hle : h ≤ g.wall := by split at hl <;> linarith
      cases Gpost with
      | nil => simp [onHead] at hp
      | cons q rest =>
        have hq := hyp.head q (by simp)
        have hq2 := hyp.post_right q (by simp)
        simp only [onHead, mem_unfilled_cons, GTier.Mem] at hp
        rcases hp with hp | hp
        · by_cases hc : p.2 ≤ q.ay + q.wall
          · exact Or.inr (Or.inr (mem_unfilled_cons.mpr (Or.inl ⟨hp.1, hp.2.1, hp.2.2.1, hc⟩)))
          · refine Or.inr (Or.inl ⟨?_, hp.2.1, ?_, ?_⟩) <;> linarith [hp.1, hp.2.2.2, hq.1, hq.2, hyp.le_W]
        · exact Or.inr (Or.inr (mem_unfilled_cons.mpr (Or.inr hp)))

/-- The region to be filled before the placement is covered by the tile and the region after it. -/
theorem StepHyp.unfilled_cover (hyp : StepHyp W Gpre g Gpost fit w h) :
    unfilled W (Gpre ++ g :: Gpost) ⊆
      (⟨g.ax, g.ay, w, h⟩ : Rect).closed ∪
        unfilled W (gpreAfter fit w Gpre ++ gmidAfter fit g w h ++ gpostAfter fit h Gpost) := by
  intro p hp
  have hn := hyp.narrow
  have hl := hyp.low
  have hw := hyp.w_pos
  have hh := hyp.h_pos
  rw [mem_unfilled_append, mem_unfilled_cons] at hp
  rw [Set.mem_union, mem_unfilled_append, mem_unfilled_append, unfilled_gpreAfter, Rect.mem_closed]
  simp only
  have hpostmono : p ∈ unfilled W Gpost → p ∈ unfilled W (gpostAfter fit h Gpost) := by
    intro hp
    unfold gpostAfter
    split
    · exact hp
    · cases Gpost with
      | nil => simp at hp
      | cons q rest =>
        simp only [onHead, mem_unfilled_cons, GTier.Mem] at hp ⊢
        rcases hp with hp | hp
        · exact Or.inl ⟨hp.1, hp.2.1, hp.2.2.1, by linarith [hp.2.2.2]⟩
        · exact Or.inr hp
  have hright : fit.narrow = false → g.ax + g.floor < p.1 → p.1 ≤ W → g.ay ≤ p.2 →
      p.2 ≤ g.ay + h → p ∈ unfilled W (gpostAfter fit h Gpost) := by
    intro hnar h1 h2 h3 h4
    unfold gpostAfter
    simp only [hnar, Bool.false_eq_true, ite_false]
    cases Gpost with
    | nil => linarith [hyp.last rfl]
    | cons q rest =>
      have hq := hyp.head q (by simp)
      have hq2 := hyp.post_right q (by simp)
      simp only [onHead, mem_unfilled_cons, GTier.Mem]
      exact Or.inl ⟨by linarith, h2, by linarith, by linarith⟩
  rcases hp with hp | hp | hp
  · exact Or.inr (Or.inl (Or.inl hp))
  · obtain ⟨p1, p2, p3, p4⟩ := hp
    cases fit <;> simp only [gmidAfter, mem_unfilled_cons, unfilled_nil, Set.mem_empty_iff_false,
      or_false, GTier.Mem, Fit.narrow, Fit.low, ite_true, Bool.false_eq_true, ite_false,
      forall_const] at hn hl hright ⊢
    · by_cases hc : g.ay + h ≤ p.2
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨p1, p2, hc, by linarith⟩)))
      · by_cases hd : p.1 ≤ g.ax + w
        · exact Or.inl ⟨p1, hd, p3, by linarith⟩
        · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨by linarith, p2, p3, by linarith⟩)))
    · by_cases hd : p.1 ≤ g.ax + w
      · exact Or.inl ⟨p1, hd, p3, by linarith⟩
      · exact Or.inr (Or.inl (Or.inr ⟨by linarith, p2, p3, p4⟩))
    · by_cases hc : g.ay + h ≤ p.2
      · exact Or.inr (Or.inl (Or.inr ⟨p1, p2, hc, by linarith⟩))
      · by_cases hd : p.1 ≤ g.ax + w
        · exact Or.inl ⟨p1, hd, p3, by linarith⟩
        · exact Or.inr (Or.inr (hright (by linarith) p2 p3 (by linarith)))
    · by_cases hd : p.1 ≤ g.ax + w
      · exact Or.inl ⟨p1, hd, p3, by linarith⟩
      · exact Or.inr (Or.inr (hright (by linarith) p2 p3 (by linarith)))
  · exact Or.inr (Or.inr (hpostmono hp))

/-- The interior of the tile does not meet the region to be filled after the placement. -/
theorem StepHyp.tile_disjoint (hyp : StepHyp W Gpre g Gpost fit w h) :
    Disjoint (⟨g.ax, g.ay, w, h⟩ : Rect).inner
      (unfilled W (gpreAfter fit w Gpre ++ gmidAfter fit g w h ++ gpostAfter fit h Gpost)) := by
  rw [Set.disjoint_left]
  intro p hpT hp
  have hn := hyp.narrow
  have hl := hyp.low
  rw [Rect.mem_inner] at hpT
  simp only at hpT
  obtain ⟨t1, t2, t3, t4⟩ := hpT
  have hwf : w ≤ g.floor := by split at hn <;> linarith
  have hhw : h ≤ g.wall := by split at hl <;> linarith
  rw [mem_unfilled_append, mem_unfilled_append, unfilled_gpreAfter] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨g', hg', hm⟩ := hp
    have := hyp.pre_above g' hg'
    linarith [hm.2.2.1]
  · cases fit <;> simp only [gmidAfter, mem_unfilled_cons, unfilled_nil, Set.mem_empty_iff_false,
      or_false, GTier.Mem] at hp
    · rcases hp with hp | hp <;> linarith [hp.1, hp.2.2.1]
    · linarith [hp.1]
    · linarith [hp.2.2.1]
  · obtain ⟨g', hg', hm⟩ := hp
    have hax : g'.ax ∈ (gpostAfter fit h Gpost).map GTier.ax := List.mem_map_of_mem hg'
    rw [map_ax_gpostAfter, List.mem_map] at hax
    obtain ⟨g'', hg'', heq⟩ := hax
    have := (hyp.post_right g'' hg'').1
    linarith [hm.1]

end Step

/-- The effect of a placement on the region to be filled, for a staircase with positive floors and walls and a tile of positive size that fits its tier. -/
theorem step_region {x W H : ℝ} {pre post : List (Tier ℝ)} {t : Tier ℝ} {mv : Placement} {side : ℝ}
    (hi : mv.tier = pre.length) (hs : Positive (pre ++ t :: post))
    (hw : 0 < (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1)
    (hh : 0 < (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2)
    (hn : mv.fit.narrow = true →
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 < t.floor)
    (hl : mv.fit.low = true →
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 < t.wall) :
    ∃ T : Rect, tileAt x W H (pre ++ t :: post) mv side = some T ∧
      T.closed ⊆ region W H (pre ++ t :: post) ∧
      region W H (place (realAlgebra x) (pre ++ t :: post) mv side) ⊆
        region W H (pre ++ t :: post) ∧
      region W H (pre ++ t :: post) ⊆
        T.closed ∪ region W H (place (realAlgebra x) (pre ++ t :: post) mv side) ∧
      Disjoint T.inner (region W H (place (realAlgebra x) (pre ++ t :: post) mv side)) := by
  have hyp : StepHyp W (geom (W - (t.floor + sumFloor post)) H pre)
      ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale, t.started⟩
      (geom W (H - sumWall pre - t.wall) post) mv.fit
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 := by
    apply stepHyp_of_positive hs hw hh
    · split
      · exact hn ‹_›
      · exact tileSize_fst_of_not_narrow _ _ _ _ _ (by simpa using ‹¬mv.fit.narrow = true›)
    · split
      · exact hl ‹_›
      · exact tileSize_snd_of_not_low _ _ _ _ _ (by simpa using ‹¬mv.fit.low = true›)
  refine ⟨_, tileAt_append x W H pre post t mv side hi, ?_, ?_, ?_, ?_⟩
  · rw [region, geom_split]
    exact hyp.tile_subset
  · rw [region, region, geom_split, geom_place x W H pre post t mv side hi]
    exact hyp.unfilled_subset
  · rw [region, region, geom_split, geom_place x W H pre post t mv side hi]
    exact hyp.unfilled_cover
  · rw [region, geom_place x W H pre post t mv side hi]
    exact hyp.tile_disjoint

end Rectiling
