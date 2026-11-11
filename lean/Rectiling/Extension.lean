-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Soundness

/-!
# Completeness of the staircase

Every tiling of the main rectangle by rectangles of proportion `x` is produced by a complete admissible placement sequence, with free sides that satisfy the emitted constraints.

The sequence is built one tile at a time.
Say that the floor of a tier *extends* when, in the tiling, the tile lying below and to the right of the right end of the floor has its top side at the level of the floor.
The next tile is placed at the first tier whose floor does not extend.
A stale tier always has a floor that extends, and a started floor never extends, which makes every such placement admissible.
-/

namespace Rectiling

/-! ### Tiles near a point -/

/-- A positive number smaller than every non-zero distance from `c` to a value in a finite list. -/
theorem exists_gap (vals : List ℝ) (c δ : ℝ) (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < δ ∧ ∀ v ∈ vals, (v ≤ c + ε → v ≤ c) ∧ (c - ε ≤ v → c ≤ v) := by
  induction vals with
  | nil => exact ⟨δ / 2, by linarith, by linarith, by simp⟩
  | cons v vs ih =>
    obtain ⟨ε, h1, h2, h3⟩ := ih
    by_cases hv : v = c
    · refine ⟨ε, h1, h2, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨fun _ => hv.le, fun _ => hv.ge⟩
      · exact h3 u hu
    · have habs : 0 < |v - c| := abs_pos.mpr (sub_ne_zero.mpr hv)
      have hle1 := min_le_left ε (|v - c| / 2)
      have hle2 := min_le_right ε (|v - c| / 2)
      refine ⟨min ε (|v - c| / 2), lt_min h1 (by linarith), lt_of_le_of_lt hle1 h2, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · constructor
        · intro h
          by_contra hc
          have : |u - c| = u - c := abs_of_pos (by linarith)
          linarith
        · intro h
          by_contra hc
          have : |u - c| = c - u := by rw [abs_of_neg (by linarith)]; ring
          linarith
      · exact ⟨fun h => (h3 u hu).1 (by linarith), fun h => (h3 u hu).2 (by linarith)⟩

variable {W H : ℝ} {tl : List Rect}

/-- A tile of a tiling that contains all points slightly above and to the right of a given point. -/
theorem IsTiling.exists_tile_above_right (h : IsTiling (Rect.main W H) tl) {cx cy : ℝ}
    (hx0 : 0 ≤ cx) (hx1 : cx < W) (hy0 : 0 ≤ cy) (hy1 : cy < H) :
    ∃ T ∈ tl, T.x ≤ cx ∧ cx < T.x + T.w ∧ T.y ≤ cy ∧ cy < T.y + T.h := by
  obtain ⟨ε1, a1, a2, a3⟩ := exists_gap (tl.map Rect.x) cx (W - cx) (by linarith)
  obtain ⟨ε2, b1, b2, b3⟩ := exists_gap (tl.map Rect.y) cy (H - cy) (by linarith)
  have hp : ((cx + ε1, cy + ε2) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
    rw [Rect.mem_closed]
    simp only [Rect.main]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨T, hT, hpT⟩ := h.exists_mem hp
  rw [Rect.mem_closed] at hpT
  simp only at hpT
  exact ⟨T, hT, (a3 T.x (List.mem_map_of_mem hT)).1 hpT.1, by linarith,
    (b3 T.y (List.mem_map_of_mem hT)).1 hpT.2.2.1, by linarith⟩

/-- A tile of a tiling that contains all points slightly below and to the right of a given point. -/
theorem IsTiling.exists_tile_below_right (h : IsTiling (Rect.main W H) tl) {cx cy : ℝ}
    (hx0 : 0 ≤ cx) (hx1 : cx < W) (hy0 : 0 < cy) (hy1 : cy ≤ H) :
    ∃ T ∈ tl, T.x ≤ cx ∧ cx < T.x + T.w ∧ T.y < cy ∧ cy ≤ T.y + T.h := by
  obtain ⟨ε1, a1, a2, a3⟩ := exists_gap (tl.map Rect.x) cx (W - cx) (by linarith)
  obtain ⟨ε2, b1, b2, b3⟩ := exists_gap (tl.map fun T => T.y + T.h) cy cy hy0
  have hp : ((cx + ε1, cy - ε2) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
    rw [Rect.mem_closed]
    simp only [Rect.main]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨T, hT, hpT⟩ := h.exists_mem hp
  rw [Rect.mem_closed] at hpT
  simp only at hpT
  exact ⟨T, hT, (a3 T.x (List.mem_map_of_mem hT)).1 hpT.1, by linarith, by linarith,
    (b3 (T.y + T.h) (List.mem_map_of_mem (f := fun T : Rect => T.y + T.h) hT)).2 hpT.2.2.2⟩

/-! ### The invariant -/

/-- Some tile has its top side at ordinate `cy`, over an interval that starts at or before abscissa `cx` and ends after it. -/
def Ext (tl : List Rect) (cx cy : ℝ) : Prop :=
  ∃ T ∈ tl, T.y + T.h = cy ∧ T.x ≤ cx ∧ cx < T.x + T.w

/-- The floor of a stale tier extends, and a started floor does not. -/
def FlagsOK (tl : List Rect) (G : List GTier) : Prop :=
  ∀ g ∈ G, (g.stale = true → Ext tl (g.ax + g.floor) g.ay) ∧
    (g.started = true → ¬Ext tl (g.ax + g.floor) g.ay)

/-- Invariant of the construction, in terms of the anchors: the tiles of the tiling are the placed ones and the remaining ones, the placed tiles lie outside the region to be filled, and the remaining ones inside it. -/
structure GInv (tl : List Rect) (W H : ℝ) (G : List GTier) (placed rem : List Rect) : Prop where
  perm : tl.Perm (placed ++ rem)
  placed_disjoint : ∀ P ∈ placed, Disjoint P.inner (unfilled W G)
  rem_subset : ∀ T ∈ rem, T.inner ⊆ unfilled W G
  subset : unfilled W G ⊆ (Rect.main W H).closed
  flags : FlagsOK tl G

/-- The structure of the anchors around a tier. -/
abbrev Around (W : ℝ) (Gpre : List GTier) (g : GTier) (Gpost : List GTier) : Prop :=
  StepHyp W Gpre g Gpost .full g.floor g.wall

theorem flagsOK_gpreAfter {fit : Fit} {w : ℝ} {G : List GTier} (hG : FlagsOK tl G)
    (hE : ∀ g ∈ G, Ext tl (g.ax + g.floor) g.ay) : FlagsOK tl (gpreAfter fit w G) := by
  have hstale : FlagsOK tl (G.map fun g => { g with stale := true }) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨fun _ => hE g' hg', (hG g' hg').2⟩
  unfold gpreAfter
  split
  · exact hstale
  · rcases List.eq_nil_or_concat G with rfl | ⟨G', a, rfl⟩
    · simp [FlagsOK]
    · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
        onLast_concat]
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hstale g (by simp only [List.concat_eq_append, List.map_append]
                           exact List.mem_append_left _ hg)
      · simp only [List.mem_singleton] at hg
        subst hg
        refine ⟨fun h => absurd h (by simp), fun h => ?_⟩
        have ha : a ∈ G'.concat a := by simp
        exact absurd (hE a ha) ((hG a ha).2 h)

theorem flagsOK_gpostAfter {fit : Fit} {h : ℝ} {G : List GTier} (hG : FlagsOK tl G) :
    FlagsOK tl (gpostAfter fit h G) := by
  unfold gpostAfter
  split
  · exact hG
  · cases G with
    | nil => exact hG
    | cons q rest =>
      intro g hg
      simp only [onHead, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hG q (by simp)
      · exact hG g (by simp [hg])

theorem flagsOK_gmidAfter {fit : Fit} {g : GTier} {w h : ℝ}
    (hE : ¬Ext tl (g.ax + g.floor) g.ay) : FlagsOK tl (gmidAfter fit g w h) := by
  have hc : g.ax + w + (g.floor - w) = g.ax + g.floor := by ring
  intro g' hg'
  cases fit <;> simp only [gmidAfter, List.mem_cons, List.not_mem_nil, or_false] at hg'
  · rcases hg' with rfl | rfl
    · simp
    · simp only [hc]
      exact ⟨fun h => absurd h (by simp), fun _ => hE⟩
  · subst hg'
    simp only [hc]
    exact ⟨fun h => absurd h (by simp), fun _ => hE⟩
  · subst hg'
    simp

theorem FlagsOK.append {G₁ G₂ : List GTier} (h₁ : FlagsOK tl G₁) (h₂ : FlagsOK tl G₂) :
    FlagsOK tl (G₁ ++ G₂) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

section GStep

variable {Gpre Gpost : List GTier} {g : GTier} {placed rem : List Rect}

theorem mem_unfilled_split {p : ℝ × ℝ} :
    p ∈ unfilled W (Gpre ++ g :: Gpost) ↔
      p ∈ unfilled W Gpre ∨ g.Mem W p ∨ p ∈ unfilled W Gpost := by
  rw [mem_unfilled_append, mem_unfilled_cons]

/-- Points to the left of the anchor or below it, close to it, are outside the region to be filled. -/
theorem Around.not_mem (A : Around W Gpre g Gpost) {p : ℝ × ℝ} (h1 : p.2 < g.ay + g.wall)
    (h2 : p.1 < g.ax ∨ p.2 < g.ay) (h3 : p.1 < g.ax + g.floor) :
    p ∉ unfilled W (Gpre ++ g :: Gpost) := by
  rw [mem_unfilled_split]
  rintro (⟨g', hg', hm⟩ | hm | ⟨g', hg', hm⟩)
  · have := A.pre_above g' hg'
    linarith [hm.2.2.1]
  · rcases h2 with h2 | h2
    · linarith [hm.1]
    · linarith [hm.2.2.1]
  · have := (A.post_right g' hg').1
    linarith [hm.1]

/-- The remaining tile whose bottom-left corner is the anchor of a tier. -/
theorem GInv.anchor_tile (htl : IsTiling (Rect.main W H) tl)
    (inv : GInv tl W H (Gpre ++ g :: Gpost) placed rem) (A : Around W Gpre g Gpost) :
    ∃ Q ∈ rem, Q.x = g.ax ∧ Q.y = g.ay := by
  have hfl : 0 < g.floor := A.w_pos
  have hwl : 0 < g.wall := A.h_pos
  have hleW := A.le_W
  -- the anchor and the top of the wall lie in the main rectangle
  have hmem : ∀ q : ℝ, g.ay ≤ q → q ≤ g.ay + g.wall → ((g.ax, q) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
    intro q hq1 hq2
    apply inv.subset
    rw [mem_unfilled_split]
    exact Or.inr (Or.inl ⟨le_refl _, by simp only; linarith, hq1, hq2⟩)
  have hm1 := hmem g.ay (le_refl _) (by linarith)
  have hm2 := hmem (g.ay + g.wall) (by linarith) (le_refl _)
  rw [Rect.mem_closed] at hm1 hm2
  simp only [Rect.main, zero_add] at hm1 hm2
  obtain ⟨T, hT, t1, t2, t3, t4⟩ := htl.exists_tile_above_right (cx := g.ax) (cy := g.ay) hm1.1
    (by linarith) hm1.2.2.1 (by linarith [hm2.2.2.2])
  have hmx1 := min_le_left (T.x + T.w) (g.ax + g.floor)
  have hmx2 := min_le_right (T.x + T.w) (g.ax + g.floor)
  have hmx3 : g.ax < min (T.x + T.w) (g.ax + g.floor) := lt_min t2 (by linarith)
  have hmy1 := min_le_left (T.y + T.h) (g.ay + g.wall)
  have hmy2 := min_le_right (T.y + T.h) (g.ay + g.wall)
  have hmy3 : g.ay < min (T.y + T.h) (g.ay + g.wall) := lt_min t4 (by linarith)
  -- the tile is not placed
  have hTrem : T ∈ rem := by
    rcases List.mem_append.mp (inv.perm.mem_iff.mp hT) with hP | hR
    · exfalso
      have hd := inv.placed_disjoint T hP
      rw [Set.disjoint_left] at hd
      refine hd (a := ((g.ax + min (T.x + T.w) (g.ax + g.floor)) / 2,
        (g.ay + min (T.y + T.h) (g.ay + g.wall)) / 2)) ?_ ?_
      · rw [Rect.mem_inner]
        simp only
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
      · rw [mem_unfilled_split]
        refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;> simp only <;> linarith
    · exact hR
  have hsub := inv.rem_subset T hTrem
  have hTx : T.x = g.ax := by
    refine le_antisymm t1 ?_
    by_contra hc
    have hc' : T.x < g.ax := not_le.mp hc
    refine A.not_mem (p := ((T.x + g.ax) / 2, (g.ay + min (T.y + T.h) (g.ay + g.wall)) / 2))
      ?_ (Or.inl ?_) ?_ (hsub ?_)
    · simp only
      linarith
    · simp only
      linarith
    · simp only
      linarith
    · rw [Rect.mem_inner]
      simp only
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hTy : T.y = g.ay := by
    refine le_antisymm t3 ?_
    by_contra hc
    have hc' : T.y < g.ay := not_le.mp hc
    refine A.not_mem (p := ((g.ax + min (T.x + T.w) (g.ax + g.floor)) / 2, (T.y + g.ay) / 2))
      ?_ (Or.inr ?_) ?_ (hsub ?_)
    · simp only
      linarith
    · simp only
      linarith
    · simp only
      linarith
    · rw [Rect.mem_inner]
      simp only
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  exact ⟨T, hTrem, hTx, hTy⟩

/-- One step of the construction, in terms of the anchors: the tile at the anchor of the first tier whose floor does not extend fits the tier, and the invariant holds after its placement. -/
theorem GInv.step (htl : IsTiling (Rect.main W H) tl)
    (inv : GInv tl W H (Gpre ++ g :: Gpost) placed rem) (A : Around W Gpre g Gpost)
    (hprevE : ∀ g' ∈ Gpre, Ext tl (g'.ax + g'.floor) g'.ay)
    (hE : ¬Ext tl (g.ax + g.floor) g.ay)
    (hlast : ∀ gp ∈ Gpre.getLast?, gp.ax + gp.floor = g.ax ∧ gp.ay = g.ay + g.wall)
    (htop : Gpre = [] → g.ay + g.wall = H) :
    ∃ Q rem', rem.Perm (Q :: rem') ∧ Q.Nondegenerate ∧ Q.x = g.ax ∧ Q.y = g.ay ∧ Q.w ≤ g.floor ∧
      Q.h ≤ g.wall ∧
      ∀ fit : Fit, (if fit.narrow then Q.w < g.floor else Q.w = g.floor) →
        (if fit.low then Q.h < g.wall else Q.h = g.wall) →
        GInv tl W H (gpreAfter fit Q.w Gpre ++ gmidAfter fit g Q.w Q.h ++ gpostAfter fit Q.h Gpost)
          (placed ++ [Q]) rem' := by
  obtain ⟨Q, hQrem, hQx, hQy⟩ := inv.anchor_tile htl A
  have hQtl : Q ∈ tl := inv.perm.mem_iff.mpr (List.mem_append_right _ hQrem)
  have hQnd := htl.nondegenerate Q hQtl
  have hQsub := htl.subset hQtl
  have hfl : 0 < g.floor := A.w_pos
  have hwl : 0 < g.wall := A.h_pos
  -- the corners of the tile lie in the main rectangle
  have hcorner : ((Q.x + Q.w, Q.y + Q.h) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
    apply hQsub
    rw [Rect.mem_closed]
    simp only
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hQnd.1, hQnd.2]
  have horigin : ((Q.x, Q.y) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
    apply hQsub
    rw [Rect.mem_closed]
    simp only
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hQnd.1, hQnd.2]
  rw [Rect.mem_closed] at hcorner horigin
  simp only [Rect.main, zero_add] at hcorner horigin
  -- the tile is not wider than the floor
  have hw : Q.w ≤ g.floor := by
    by_contra hc
    have hc' : g.floor < Q.w := not_le.mp hc
    apply hE
    have hpost : Gpost ≠ [] := by
      intro hnil
      have := A.last hnil
      linarith [hcorner.2.1]
    obtain ⟨q, rest, rfl⟩ := List.exists_cons_of_ne_nil hpost
    have hq := A.head q (by simp)
    have hq2 := A.post_right q (by simp)
    have hqmem : ((q.ax, q.ay) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
      apply inv.subset
      rw [mem_unfilled_split]
      refine Or.inr (Or.inr (mem_unfilled_cons.mpr (Or.inl ⟨le_refl _, ?_, le_refl _, ?_⟩)))
      · simp only
        linarith [hcorner.2.1]
      · simp only
        linarith
    rw [Rect.mem_closed] at hqmem
    simp only [Rect.main, zero_add] at hqmem
    have hwq : 0 < q.wall := hq2.2.2
    obtain ⟨T, hT, s1, s2, s3, s4⟩ := htl.exists_tile_below_right (cx := g.ax + g.floor)
      (cy := g.ay) (by linarith [horigin.1]) (by linarith [hcorner.2.1]) (by linarith [hqmem.2.2.1])
      (by linarith [horigin.2.2.2])
    refine ⟨T, hT, ?_, s1, s2⟩
    refine le_antisymm ?_ s4
    by_contra hc2
    have hc2' : g.ay < T.y + T.h := not_le.mp hc2
    have hTQ : T = Q := by
      apply htl.eq_of_not_disjoint hT hQtl
      apply Rect.not_disjoint_inner_of_overlap
      · rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨by linarith [htl.nondegenerate T hT |>.1], by linarith⟩,
          ⟨by linarith, by linarith [hQnd.1]⟩⟩
      · rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨by linarith, by linarith [hQnd.2]⟩, ⟨by linarith, by linarith [hQnd.2]⟩⟩
    rw [hTQ] at s3
    linarith
  -- the tile is not higher than the wall
  have hh : Q.h ≤ g.wall := by
    rcases List.eq_nil_or_concat Gpre with rfl | ⟨G', gp, rfl⟩
    · have := htop rfl
      linarith [hcorner.2.2.2]
    · have hgp := hlast gp (by simp)
      obtain ⟨T, hT, s1, s2, s3⟩ := hprevE gp (by simp)
      by_contra hc
      have hc' : g.wall < Q.h := not_le.mp hc
      have hTnd := htl.nondegenerate T hT
      have hTQ : T = Q := by
        apply htl.eq_of_not_disjoint hT hQtl
        apply Rect.not_disjoint_inner_of_overlap
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith [hTnd.1], by linarith [hQnd.1]⟩, ⟨by linarith, by linarith [hQnd.1]⟩⟩
        · rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨by linarith [hTnd.2], by linarith [hTnd.2]⟩, ⟨by linarith, by linarith [hQnd.2]⟩⟩
      rw [hTQ] at s1
      linarith
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hQrem
  refine ⟨Q, l₁ ++ l₂, List.perm_middle, hQnd, hQx, hQy, hw, hh, ?_⟩
  intro fit hn hl
  have hyp : StepHyp W Gpre g Gpost fit Q.w Q.h :=
    ⟨A.pre_above, A.post_right, A.head, A.last, A.le_W, hQnd.1, hQnd.2, hn, hl⟩
  have hQeq : (⟨g.ax, g.ay, Q.w, Q.h⟩ : Rect) = Q := by
    ext <;> simp [hQx, hQy]
  have h1 := hyp.unfilled_subset
  have h2 := hyp.unfilled_cover
  have h3 := hyp.tile_disjoint
  rw [hQeq] at h2 h3
  have hperm : tl.Perm (placed ++ [Q] ++ (l₁ ++ l₂)) := by
    refine inv.perm.trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left placed List.perm_middle
  refine ⟨hperm, ?_, ?_, h1.trans inv.subset, ?_⟩
  · intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact (inv.placed_disjoint P hP).mono_right h1
    · simp only [List.mem_singleton] at hP
      subst hP
      exact h3
  · intro T hT p hp
    have hTrem : T ∈ l₁ ++ Q :: l₂ := by
      rcases List.mem_append.mp hT with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hTtl : T ∈ tl := hperm.mem_iff.mpr (List.mem_append_right _ hT)
    rcases h2 (inv.rem_subset T hTrem hp) with hq | hq
    · exfalso
      have hpw : (placed ++ [Q] ++ (l₁ ++ l₂)).Pairwise fun S T => Disjoint S.inner T.inner :=
        (hperm.pairwise_iff fun h => h.symm).mp htl.disjoint
      rw [List.pairwise_append] at hpw
      have hQT : Disjoint Q.inner T.inner := hpw.2.2 Q (by simp) T hT
      have hsep := Rect.separated_of_disjoint hQnd (htl.nondegenerate T hTtl) hQT
      rw [Rect.mem_inner] at hp
      rw [Rect.mem_closed] at hq
      rcases hsep with h | h | h | h <;> linarith [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hq.1, hq.2.1,
        hq.2.2.1, hq.2.2.2]
    · exact hq
  · have hflags := inv.flags
    have hpre : FlagsOK tl Gpre := fun g' hg' => hflags g' (by simp [hg'])
    have hpost : FlagsOK tl Gpost := fun g' hg' => hflags g' (by simp [hg'])
    exact ((flagsOK_gpreAfter hpre hprevE).append (flagsOK_gmidAfter hE)).append
      (flagsOK_gpostAfter hpost)

end GStep

end Rectiling
