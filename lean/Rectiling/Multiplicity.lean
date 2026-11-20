-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Records

/-!
# The number of records of a tiling

For every set of crossings of a similar tiling there is exactly one complete admissible record that yields the tiling and places the tile to the upper left before the tile to the lower right exactly at the crossings of the set.
Hence a tiling with `k` crossings is yielded by exactly `2 ^ k` records, for each choice of orientations.

The record of a set `X` of crossings is built as in the proof of completeness, with the first tier whose floor does not extend to a point outside `X` in the place of the first tier whose floor does not extend.
-/

namespace Rectiling

open scoped List

variable {x W H : ℝ} {tl : List Rect}

/-! ### The invariant of the construction -/

/-- Invariant of the construction, without the flags: the tiles of the tiling are the placed ones and the remaining ones, the placed tiles lie outside the region to be filled, and the remaining ones inside it. -/
structure SInv (tl : List Rect) (W H : ℝ) (G : List GTier) (placed rem : List Rect) : Prop where
  perm : tl.Perm (placed ++ rem)
  placed_disjoint : ∀ P ∈ placed, Disjoint P.inner (unfilled W G)
  rem_subset : ∀ T ∈ rem, T.inner ⊆ unfilled W G
  subset : unfilled W G ⊆ (Rect.main W H).closed

/-- The end of the floor of a stale tier has the given property, and the end of a started floor does not. -/
def FlagsX (E : ℝ × ℝ → Prop) (G : List GTier) : Prop :=
  ∀ g ∈ G, (g.stale = true → E g.tip) ∧ (g.started = true → ¬E g.tip)

section Flags

variable {E : ℝ × ℝ → Prop}

theorem flagsX_gpreAfter {fit : Fit} {w : ℝ} {G : List GTier} (hG : FlagsX E G)
    (hE : ∀ g ∈ G, E g.tip) : FlagsX E (gpreAfter fit w G) := by
  have hstale : FlagsX E (G.map fun g => { g with stale := true }) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨fun _ => hE g' hg', (hG g' hg').2⟩
  unfold gpreAfter
  split
  · exact hstale
  · rcases List.eq_nil_or_concat G with rfl | ⟨G', a, rfl⟩
    · simp [FlagsX]
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

theorem flagsX_gpostAfter {fit : Fit} {h : ℝ} {G : List GTier} (hG : FlagsX E G) :
    FlagsX E (gpostAfter fit h G) := by
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

theorem flagsX_gmidAfter {fit : Fit} {g : GTier} {w h : ℝ} (hE : ¬E g.tip) :
    FlagsX E (gmidAfter fit g w h) := by
  have hc : ∀ h' : ℝ, (⟨g.ax + w, g.ay, g.floor - w, h', false, true⟩ : GTier).tip = g.tip := by
    intro h'
    simp only [GTier.tip, Prod.mk.injEq, and_true]
    ring
  intro g' hg'
  cases fit <;> simp only [gmidAfter, List.mem_cons, List.not_mem_nil, or_false] at hg'
  · rcases hg' with rfl | rfl
    · simp
    · rw [hc]
      exact ⟨fun h => absurd h (by simp), fun _ => hE⟩
  · subst hg'
    rw [hc]
    exact ⟨fun h => absurd h (by simp), fun _ => hE⟩
  · subst hg'
    simp

theorem FlagsX.append {G₁ G₂ : List GTier} (h₁ : FlagsX E G₁) (h₂ : FlagsX E G₂) :
    FlagsX E (G₁ ++ G₂) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

end Flags

section SStep

variable {Gpre Gpost : List GTier} {g : GTier} {placed rem : List Rect}

/-- The remaining tile whose bottom-left corner is the anchor of a tier. -/
theorem SInv.anchor_tile (htl : IsTiling (Rect.main W H) tl)
    (inv : SInv tl W H (Gpre ++ g :: Gpost) placed rem) (A : Around W Gpre g Gpost) :
    ∃ Q ∈ rem, Q.x = g.ax ∧ Q.y = g.ay := by
  have hfl : 0 < g.floor := A.w_pos
  have hwl : 0 < g.wall := A.h_pos
  have hleW := A.le_W
  have hmem : ∀ q : ℝ, g.ay ≤ q → q ≤ g.ay + g.wall →
      ((g.ax, q) : ℝ × ℝ) ∈ (Rect.main W H).closed := by
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

/-- One step of the construction, in terms of the anchors: at a tier such that the floors of the tiers before it extend, and such that the end of its floor is the bottom-right corner of a tile if the floor extends, the tile at the anchor fits the tier, and the invariant holds after its placement. -/
theorem SInv.step (htl : IsTiling (Rect.main W H) tl)
    (inv : SInv tl W H (Gpre ++ g :: Gpost) placed rem) (A : Around W Gpre g Gpost)
    (hprevE : ∀ g' ∈ Gpre, Ext tl (g'.ax + g'.floor) g'.ay)
    (hE : Ext tl (g.ax + g.floor) g.ay → ∃ V ∈ tl, V.UpperLeftOf g.tip)
    (hlast : ∀ gp ∈ Gpre.getLast?, gp.ax + gp.floor = g.ax ∧ gp.ay = g.ay + g.wall)
    (htop : Gpre = [] → g.ay + g.wall = H) :
    ∃ Q rem', rem.Perm (Q :: rem') ∧ Q.Nondegenerate ∧ Q.x = g.ax ∧ Q.y = g.ay ∧ Q.w ≤ g.floor ∧
      Q.h ≤ g.wall ∧
      ∀ fit : Fit, (if fit.narrow then Q.w < g.floor else Q.w = g.floor) →
        (if fit.low then Q.h < g.wall else Q.h = g.wall) →
        SInv tl W H (gpreAfter fit Q.w Gpre ++ gmidAfter fit g Q.w Q.h ++ gpostAfter fit Q.h Gpost)
          (placed ++ [Q]) rem' := by
  obtain ⟨Q, hQrem, hQx, hQy⟩ := inv.anchor_tile htl A
  have hQtl : Q ∈ tl := inv.perm.mem_iff.mpr (List.mem_append_right _ hQrem)
  have hQnd := htl.nondegenerate Q hQtl
  have hQsub := htl.subset hQtl
  have hfl : 0 < g.floor := A.w_pos
  have hwl : 0 < g.wall := A.h_pos
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
    have hext : Ext tl (g.ax + g.floor) g.ay := by
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
        (cy := g.ay) (by linarith [horigin.1]) (by linarith [hcorner.2.1])
        (by linarith [hqmem.2.2.1]) (by linarith [horigin.2.2.2])
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
    -- the end of the floor is the bottom-right corner of a tile, which is the tile at the anchor
    obtain ⟨V, hV, hVx, hVy⟩ := hE hext
    simp only [GTier.tip] at hVx hVy
    obtain ⟨hVw, hVh⟩ := htl.nondegenerate V hV
    obtain ⟨hQw, hQh⟩ := hQnd
    have hVQ : V = Q := by
      apply htl.eq_of_not_disjoint hV hQtl
      apply Rect.not_disjoint_inner_of_overlap
      · rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      · rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    rw [hVQ] at hVx
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
  refine ⟨hperm, ?_, ?_, h1.trans inv.subset⟩
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

end SStep

/-! ### One step of the construction -/

/-- The first tier whose floor does not extend to a point outside the given set. -/
theorem exists_first_tierX (htl : IsTiling (Rect.main W H) tl) (X : Set (ℝ × ℝ))
    {s : List (Tier ℝ)} (hs : s ≠ []) :
    ∃ pre t post, s = pre ++ t :: post ∧
      (∀ g' ∈ geom (W - (t.floor + sumFloor post)) H pre, XExt tl X g'.tip) ∧
      ¬XExt tl X (⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall,
        t.stale, t.started⟩ : GTier).tip := by
  have hex : ∃ g ∈ geom W H s, ¬XExt tl X g.tip := by
    obtain ⟨pre, t, post, rfl, -, hn⟩ := exists_first_tier htl hs
    refine ⟨⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale,
      t.started⟩, ?_, fun h => hn h.1⟩
    rw [geom_split]
    simp
  obtain ⟨G₁, g, G₂, hG, h1, h2⟩ := exists_first_not _ _ hex
  have hlen : G₁.length < s.length := by
    have := congrArg List.length hG
    simp only [length_geom, List.length_append, List.length_cons] at this
    omega
  obtain ⟨t, ht⟩ : ∃ t, s[G₁.length]? = some t := ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨pre, post, rfl, hn⟩ := exists_split ht
  rw [geom_split] at hG
  obtain ⟨e1, e2⟩ := List.append_inj hG (by simp [hn])
  simp only [List.cons.injEq] at e2
  obtain ⟨e2, -⟩ := e2
  subst e1 e2
  exact ⟨pre, _, post, rfl, h1, h2⟩

/-- Invariant of the construction of the record of a set of points: floors and walls are positive, the invariant on the anchors holds, the floor of every stale tier extends to a point outside the set, and the floor of no started tier does. -/
structure XState (tl : List Rect) (X : Set (ℝ × ℝ)) (W H : ℝ) (s : List (Tier ℝ))
    (placed rem : List Rect) : Prop where
  pos : Positive s
  sinv : SInv tl W H (geom W H s) placed rem
  flags : FlagsX (XExt tl X) (geom W H s)

/-- One step of the construction: a placement at the first tier whose floor does not extend to a point outside the set, which obeys the rules, whose tile is one of the remaining tiles of the tiling, with its chosen orientation, and whose constraints hold, and after which the invariant holds. -/
theorem XState.step (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {ori : Rect → Bool}
    (hori : ∀ T ∈ tl, (ori T = false → T.w = x * T.h) ∧ (ori T = true → T.h = x * T.w))
    {X : Set (ℝ × ℝ)} (hX : ∀ q ∈ X, ∃ V ∈ tl, V.UpperLeftOf q) {s : List (Tier ℝ)}
    {placed rem : List Rect} (inv : XState tl X W H s placed rem) (hs : s ≠ []) :
    ∃ (mv : Placement) (side : ℝ) (Q : Rect) (rem' : List Rect), rem.Perm (Q :: rem') ∧
      mv.tall = ori Q ∧ FirstNot (fun g => XExt tl X g.tip) (geom W H s) mv.tier ∧
      ∀ side', (mv.fit = .inside → side' = side) →
        Allows s mv ∧ tileAt x W H s mv side' = some Q ∧ (∀ c ∈ positiveAt s mv side', 0 < c) ∧
          (∀ e ∈ equationAt (realAlgebra x) s mv, e = 0) ∧
          XState tl X W H (place (realAlgebra x) s mv side') (placed ++ [Q]) rem' := by
  obtain ⟨pre, t, post, rfl, hprevE, hE⟩ := exists_first_tierX htl X hs
  have ht := inv.pos t (by simp)
  have A : Around W (geom (W - (t.floor + sumFloor post)) H pre)
      ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale,
        t.started⟩ (geom W (H - sumWall pre - t.wall) post) :=
    stepHyp_of_positive inv.pos ht.1 ht.2 (by simp [Fit.narrow]) (by simp [Fit.low])
  have sinv := inv.sinv
  have flags := inv.flags
  rw [geom_split] at sinv flags
  have hlast : ∀ gp ∈ (geom (W - (t.floor + sumFloor post)) H pre).getLast?,
      gp.ax + gp.floor = W - (t.floor + sumFloor post) ∧
        gp.ay = H - sumWall pre - t.wall + t.wall := by
    intro gp hgp
    rcases List.eq_nil_or_concat pre with rfl | ⟨l, p, rfl⟩
    · simp [geom] at hgp
    · rw [List.concat_eq_append, geom_concat] at hgp
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
        Option.some.injEq] at hgp
      subst hgp
      simp only [List.concat_eq_append, sumWall_append, sumWall_cons, sumWall_nil]
      constructor <;> ring
  have htop : geom (W - (t.floor + sumFloor post)) H pre = [] →
      H - sumWall pre - t.wall + t.wall = H := by
    intro hnil
    have : pre = [] := by
      have := congrArg List.length hnil
      simpa using this
    subst this
    simp
  have hE' : Ext tl (W - (t.floor + sumFloor post) + t.floor) (H - sumWall pre - t.wall) →
      ∃ V ∈ tl, V.UpperLeftOf (⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor,
        t.wall, t.stale, t.started⟩ : GTier).tip := by
    intro hext
    by_contra hc
    exact hE ⟨hext, fun hmem => hc (hX _ hmem)⟩
  obtain ⟨Q, rem', hperm, hQnd, hQx, hQy, hw, hh, hG⟩ :=
    sinv.step htl A (fun g' hg' => (hprevE g' hg').1) hE' hlast htop
  simp only at hQx hQy hw hh
  have hQtl : Q ∈ tl := inv.sinv.perm.mem_iff.mpr
    (List.mem_append_right _ (hperm.mem_iff.mpr (by simp)))
  obtain ⟨tall, htall0, htall1, htall2⟩ : ∃ tall : Bool, tall = ori Q ∧
      (tall = false → Q.w = x * Q.h) ∧ (tall = true → Q.h = x * Q.w) :=
    ⟨ori Q, rfl, (hori Q hQtl).1, (hori Q hQtl).2⟩
  obtain ⟨fit, hn, hl⟩ : ∃ fit : Fit, (if fit.narrow then Q.w < t.floor else Q.w = t.floor) ∧
      (if fit.low then Q.h < t.wall else Q.h = t.wall) := by
    by_cases h1 : Q.w < t.floor <;> by_cases h2 : Q.h < t.wall
    · exact ⟨.inside, by simpa [Fit.narrow] using h1, by simpa [Fit.low] using h2⟩
    · exact ⟨.fullHeight, by simpa [Fit.narrow] using h1,
        by simpa [Fit.low] using le_antisymm hh (not_lt.mp h2)⟩
    · exact ⟨.fullWidth, by simpa [Fit.narrow] using le_antisymm hw (not_lt.mp h1),
        by simpa [Fit.low] using h2⟩
    · exact ⟨.full, by simpa [Fit.narrow] using le_antisymm hw (not_lt.mp h1),
        by simpa [Fit.low] using le_antisymm hh (not_lt.mp h2)⟩
  have hn1 : fit.narrow = true → Q.w < t.floor := fun h => by simpa [h] using hn
  have hn2 : fit.narrow = false → Q.w = t.floor := fun h => by simpa [h] using hn
  have hl1 : fit.low = true → Q.h < t.wall := fun h => by simpa [h] using hl
  have hl2 : fit.low = false → Q.h = t.wall := fun h => by simpa [h] using hl
  have hfn := (firstNot_split (P := fun g => XExt tl X g.tip)
    (Gpost := geom W (H - sumWall pre - t.wall) post)).mpr ⟨hprevE, hE⟩
  rw [length_geom] at hfn
  refine ⟨⟨pre.length, fit, tall⟩, if tall then Q.w else Q.h, Q, rem', hperm, htall0, ?_, ?_⟩
  · rw [geom_split]
    exact hfn
  intro side' hside
  have hsize : tileSize (realAlgebra x) fit tall t.floor t.wall side' = (Q.w, Q.h) :=
    tileSize_of_tile hx htall1 htall2 hn2 hl2 hside
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [allows_append rfl]
    constructor
    · by_contra hc
      have hst : t.stale = true := by simpa using hc
      have hflag := flags ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor,
        t.wall, t.stale, t.started⟩ (by simp)
      exact hE (hflag.1 hst)
    · intro _ p hp
      rcases List.eq_nil_or_concat pre with rfl | ⟨l, p', rfl⟩
      · simp at hp
      · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
          Option.some_or, Option.mem_def, Option.some.injEq] at hp
        subst hp
        have hmem : (⟨W - (t.floor + sumFloor post) - p'.floor, H - sumWall l - p'.wall, p'.floor,
            p'.wall, p'.stale, p'.started⟩ : GTier) ∈
            geom (W - (t.floor + sumFloor post)) H (l.concat p') := by
          rw [List.concat_eq_append, geom_concat]
          simp
        by_contra hc
        have hst : p'.started = true := by simpa using hc
        exact (flags _ (List.mem_append_left _ hmem)).2 hst (hprevE _ hmem)
  · rw [tileAt_append x W H pre post t _ side' rfl]
    dsimp only
    rw [hsize]
    simp only [Option.some.injEq]
    ext <;> simp [hQx, hQy]
  · intro c hc
    rw [positiveAt_append pre post t _ side' rfl] at hc
    simp only [Option.mem_def, Option.some.injEq] at hc
    subst hc
    cases fit <;> simp only [positiveOf]
    · rw [hside rfl]
      split
      · exact hQnd.1
      · exact hQnd.2
    · exact ht.2
    · exact ht.1
    · exact ht.1
  · intro e he
    rw [equationAt_append _ pre post t _ rfl] at he
    dsimp only at he
    cases fit <;> cases tall <;>
      simp only [equationOf, Option.mem_def, Option.some.injEq, reduceCtorEq, realAlgebra] at he
    · subst he
      rw [← hn2 rfl, ← hl2 rfl, htall1 rfl]
      ring
    · subst he
      rw [← hn2 rfl, ← hl2 rfl, htall2 rfl]
      ring
  · rw [place_append _ pre post t _ side' rfl]
    dsimp only
    rw [hsize]
    exact positive_parts inv.pos hQnd.1 hQnd.2 hn1 hl1
  · rw [geom_place x W H pre post t _ side' rfl]
    dsimp only
    rw [hsize]
    exact hG fit hn hl
  · rw [geom_place x W H pre post t _ side' rfl]
    dsimp only
    rw [hsize]
    have hpre : FlagsX (XExt tl X) (geom (W - (t.floor + sumFloor post)) H pre) :=
      fun g' hg' => flags g' (by simp [hg'])
    have hpost : FlagsX (XExt tl X) (geom W (H - sumWall pre - t.wall) post) :=
      fun g' hg' => flags g' (by simp [hg'])
    exact ((flagsX_gpreAfter hpre hprevE).append (flagsX_gmidAfter hE)).append
      (flagsX_gpostAfter hpost)

/-! ### The construction -/

theorem chooses_congr {X : Set (ℝ × ℝ)} {f g : ℕ → ℝ} (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), (∀ j, k ≤ j → f j = g j) →
      (Chooses tl X x W H f s k path ↔ Chooses tl X x W H g s k path) := by
  induction path with
  | nil =>
    intro s k _
    exact Iff.rfl
  | cons mv rest ih =>
    intro s k hfg
    have hk := hfg k (le_refl k)
    have := ih (place (realAlgebra x) s mv (g k)) (nextIndex k mv)
      fun j hj => hfg j ((le_nextIndex k mv).trans hj)
    simp only [Chooses, hk, this]

/-- From any state satisfying the invariant, the remaining tiles are produced by a sequence of placements that obeys the rules, empties the staircase, has the chosen orientations, whose constraints hold, and each of which is made at the first tier whose floor does not extend to a point outside the set. -/
theorem complete_fromX (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {ori : Rect → Bool}
    (hori : ∀ T ∈ tl, (ori T = false → T.w = x * T.h) ∧ (ori T = true → T.h = x * T.w))
    {X : Set (ℝ × ℝ)} (hX : ∀ q ∈ X, ∃ V ∈ tl, V.UpperLeftOf q) :
    ∀ (n : ℕ) (s : List (Tier ℝ)) (k : ℕ) (placed rem : List Rect), rem.length = n →
      XState tl X W H s placed rem →
      ∃ (path : List Placement) (fresh : ℕ → ℝ), Allowed (realAlgebra x) fresh s k path ∧
        Satisfies x fresh s k path ∧ (tiles x W H fresh s k path).Perm rem ∧
        List.Forall₂ (fun mv T => mv.tall = ori T) path (tiles x W H fresh s k path) ∧
        Chooses tl X x W H fresh s k path := by
  intro n
  induction n with
  | zero =>
    intro s k placed rem hlen inv
    have hrem : rem = [] := List.length_eq_zero_iff.mp hlen
    subst hrem
    have hs : s = [] := by
      by_contra hs
      obtain ⟨mv, side, Q, rem', hperm, -⟩ := inv.step hx htl hori hX hs
      simpa using hperm.length_eq
    subst hs
    exact ⟨[], fun _ => 0, rfl, ⟨by simp [positives], by simp [equations]⟩, by simp [tiles],
      List.Forall₂.nil, trivial⟩
  | succ n ih =>
    intro s k placed rem hlen inv
    have hs : s ≠ [] := by
      rintro rfl
      obtain ⟨T, rest, rfl⟩ := List.exists_cons_of_ne_nil (l := rem) (by
        intro h
        simp [h] at hlen)
      have hT : T ∈ tl := inv.sinv.perm.mem_iff.mpr (by simp)
      have hnd := htl.nondegenerate T hT
      have hsub := inv.sinv.rem_subset T (by simp)
      have hp : ((T.x + T.w / 2, T.y + T.h / 2) : ℝ × ℝ) ∈ T.inner := by
        rw [Rect.mem_inner]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith [hnd.1, hnd.2]
      have := hsub hp
      simp [geom] at this
    obtain ⟨mv, side, Q, rem', hperm, hori', hfn, hstep⟩ := inv.step hx htl hori hX hs
    have hlen' : rem'.length = n := by
      have := hperm.length_eq
      simp only [List.length_cons] at this
      omega
    obtain ⟨-, -, -, -, hinv'⟩ := hstep side fun _ => rfl
    obtain ⟨path', fresh', a1, a2, a3, a4, a5⟩ :=
      ih (place (realAlgebra x) s mv side) (nextIndex k mv) (placed ++ [Q]) rem' hlen' hinv'
    have key : ∀ fresh : ℕ → ℝ, (mv.fit = .inside → fresh k = side) →
        place (realAlgebra x) s mv (fresh k) = place (realAlgebra x) s mv side →
        (∀ j, nextIndex k mv ≤ j → fresh j = fresh' j) →
        ∃ (path : List Placement) (fresh : ℕ → ℝ), Allowed (realAlgebra x) fresh s k path ∧
          Satisfies x fresh s k path ∧ (tiles x W H fresh s k path).Perm rem ∧
          List.Forall₂ (fun mv T => mv.tall = ori T) path (tiles x W H fresh s k path) ∧
          Chooses tl X x W H fresh s k path := by
      intro fresh hside hplace hagree
      obtain ⟨b1, b2, b3, b4, -⟩ := hstep (fresh k) hside
      obtain ⟨c1, c2, c3⟩ := run_congr (realAlgebra x) path' (place (realAlgebra x) s mv side)
        (nextIndex k mv) fun j hj _ => hagree j hj
      have c4 := tiles_congr (x := x) (W := W) (H := H) path' (place (realAlgebra x) s mv side)
        (nextIndex k mv) hagree
      have c5 := chooses_congr (tl := tl) (X := X) (x := x) (W := W) (H := H) path'
        (place (realAlgebra x) s mv side) (nextIndex k mv) hagree
      refine ⟨mv :: path', fresh, ⟨b1, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨hfn, ?_⟩⟩
      · rw [hplace]
        exact c1.mpr a1
      · intro c hc
        simp only [positives, hplace, c2, List.mem_append, Option.mem_toList] at hc
        rcases hc with hc | hc
        · exact b3 c hc
        · exact a2.1 c hc
      · intro e he
        simp only [equations, hplace, c3, List.mem_append, Option.mem_toList] at he
        rcases he with he | he
        · exact b4 e he
        · exact a2.2 e he
      · simp only [tiles, b2, hplace, c4, Option.toList_some, List.singleton_append]
        exact (List.Perm.cons Q a3).trans hperm.symm
      · simp only [tiles, b2, hplace, c4, Option.toList_some, List.singleton_append]
        exact List.Forall₂.cons hori' a4
      · rw [hplace]
        exact c5.mpr a5
    by_cases hfit : mv.fit = .inside
    · refine key (Function.update fresh' k side) (fun _ => by simp) (by simp) ?_
      intro j hj
      have : j ≠ k := by
        simp only [nextIndex, hfit, ite_true] at hj
        omega
      simp [Function.update_of_ne this]
    · exact key fresh' (fun h => absurd h hfit) (place_side _ s mv _ _ hfit) fun _ _ => rfl

/-- A record that yields the tiling and makes each placement at the first tier whose floor does not extend to a point outside a given set of crossings. -/
theorem exists_chooses (hW : 0 < W) (hH : 0 < H) (h : IsSimilarTiling x (Rect.main W H) tl)
    {ori : Rect → Bool}
    (hori : ∀ T ∈ tl, (ori T = false → T.w = x * T.h) ∧ (ori T = true → T.h = x * T.w))
    {X : Set (ℝ × ℝ)} (hX : ∀ q ∈ X, IsCrossing tl q) :
    ∃ (path : List Placement) (fresh : ℕ → ℝ), YieldsWith x W H tl ori path fresh ∧
      Chooses tl X x W H fresh (initial W H) 0 path := by
  have hx : 0 < x := by linarith [h.one_le]
  have htl := h.toIsTiling
  have inv : XState tl X W H (initial W H) [] tl := by
    refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro t ht
      simp only [initial, List.mem_singleton] at ht
      subst ht
      exact ⟨hW, hH⟩
    · simp
    · simp
    · intro T hT
      change T.inner ⊆ region W H (initial W H)
      rw [region_initial]
      exact (Rect.inner_subset_closed T).trans (htl.subset hT)
    · change region W H (initial W H) ⊆ _
      rw [region_initial]
    · simp [FlagsX, initial, geom]
  have hX' : ∀ q ∈ X, ∃ V ∈ tl, V.UpperLeftOf q := by
    intro q hq
    obtain ⟨U, hU, V, hV, hUq, hVq⟩ := (isCrossing_iff htl).mp (hX q hq)
    exact ⟨V, hV, hVq⟩
  obtain ⟨path, fresh, a1, a2, a3, a4, a5⟩ :=
    complete_fromX hx htl hori hX' tl.length (initial W H) 0 [] tl rfl inv
  have hlen : path.length = tl.length := a4.length_eq.trans a3.length_eq
  have hunit := (allowed_map (Algebra.isHom_unit (realAlgebra x)) fresh (initial W H) 0 path).mpr a1
  have hcomp := (Allowed.completeFrom path _ 0 hunit).2
  rw [hlen] at hcomp
  exact ⟨path, fresh, ⟨hcomp, a2, a3, a4⟩, a5⟩

/-! ### The order of placement at the crossings -/

/-- In a record that makes each placement at the first tier whose floor does not extend to a point outside a set, a point at which the tile to the lower right is placed first is not in the set, and a point at which the tile to the upper left is placed first is in it. -/
theorem Placing.order (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {X : Set (ℝ × ℝ)}
    {fresh : ℕ → ℝ} (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), Placing x W H tl fresh s k path →
      Chooses tl X x W H fresh s k path →
      ∀ (q : ℝ × ℝ) (U V : Rect), U.LowerRightOf q → V.UpperLeftOf q →
        ([U, V] <+ tiles x W H fresh s k path → q ∉ X) ∧
          ([V, U] <+ tiles x W H fresh s k path → q ∈ X) := by
  induction path with
  | nil =>
    intro s k _ _ q U V _ _
    simp [tiles]
  | cons mv rest ih =>
    intro s k r c q U V hUq hVq
    obtain ⟨Gpre, g, Gpost, Q, hgeom, htier, hQ, -, rtail, hd⟩ := r.head hx
    obtain ⟨cf, ct⟩ := c
    rw [hgeom, htier, firstNot_split] at cf
    obtain ⟨cpre, cself⟩ := cf
    obtain ⟨ih1, ih2⟩ := ih _ _ rtail ct q U V hUq hVq
    rw [tiles_cons hQ, pair_sublist_cons, pair_sublist_cons]
    obtain ⟨hUx, hUy⟩ := hUq
    obtain ⟨hVx, hVy⟩ := hVq
    obtain ⟨hQw, hQh⟩ := hd.nondegenerate
    have hfl := hd.around.w_pos
    have hwl := hd.around.h_pos
    have hqx := hd.qx
    have hqy := hd.qy
    have hwle : Q.w ≤ g.floor := by
      have := hd.hyp.narrow
      split at this <;> linarith
    have hhle : Q.h ≤ g.wall := by
      have := hd.hyp.low
      split at this <;> linarith
    constructor
    · rintro (h | ⟨rfl, hV⟩)
      · exact ih1 h
      · -- the tile to the lower right is placed now: it is as high as the wall
        obtain ⟨hVtl, hVsub⟩ := hd.sub V (List.mem_cons_of_mem _ hV)
        obtain ⟨hVw, hVh⟩ := htl.nondegenerate V hVtl
        obtain ⟨-, -, -, hVH⟩ := htl.bounds hVtl
        have hUh : U.h = g.wall := by
          refine le_antisymm hhle ?_
          by_contra hc
          have hc' := not_le.mp hc
          have n1 := min_le_left (V.y + V.h) (g.ay + g.wall)
          have n2 := min_le_right (V.y + V.h) (g.ay + g.wall)
          have n3 : V.y < min (V.y + V.h) (g.ay + g.wall) := lt_min (by linarith) (by linarith)
          refine hd.around.not_mem (p := ((V.x + (V.x + V.w)) / 2,
            (V.y + min (V.y + V.h) (g.ay + g.wall)) / 2)) ?_ (Or.inl ?_) ?_ (hVsub ?_)
          · simp only
            linarith
          · simp only
            linarith
          · simp only
            linarith
          · rw [Rect.mem_closed]
            simp only
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
        rcases List.eq_nil_or_concat Gpre with rfl | ⟨G₁, gp, rfl⟩
        · have := hd.top rfl
          linarith
        · obtain ⟨hl1, hl2⟩ := hd.last gp (by simp)
          have hgp := cpre gp (by simp)
          have htip : gp.tip = q :=
            Prod.ext (by simp only [GTier.tip]; linarith) (by simp only [GTier.tip]; linarith)
          rw [htip] at hgp
          exact hgp.2
    · rintro (h | ⟨rfl, hU⟩)
      · exact ih2 h
      · -- the tile to the upper left is placed now: it is as wide as the floor
        obtain ⟨hUtl, hUsub⟩ := hd.sub U (List.mem_cons_of_mem _ hU)
        obtain ⟨hUw, hUh⟩ := htl.nondegenerate U hUtl
        have hVw : V.w = g.floor := by
          refine le_antisymm hwle ?_
          by_contra hc
          have hc' := not_le.mp hc
          have n1 := min_le_left (U.x + U.w) (g.ax + g.floor)
          have n2 := min_le_right (U.x + U.w) (g.ax + g.floor)
          have n3 : U.x < min (U.x + U.w) (g.ax + g.floor) := lt_min (by linarith) (by linarith)
          refine hd.around.not_mem (p := ((U.x + min (U.x + U.w) (g.ax + g.floor)) / 2,
            (U.y + (U.y + U.h)) / 2)) ?_ (Or.inr ?_) ?_ (hUsub ?_)
          · simp only
            linarith
          · simp only
            linarith
          · simp only
            linarith
          · rw [Rect.mem_closed]
            simp only
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
        have htip : g.tip = q :=
          Prod.ext (by simp only [GTier.tip]; linarith) (by simp only [GTier.tip]; linarith)
        by_contra hnX
        refine cself ⟨⟨U, hUtl, ?_, ?_, ?_⟩, by rw [htip]; exact hnX⟩
        · simp only [GTier.tip]
          linarith
        · simp only [GTier.tip]
          linarith
        · simp only [GTier.tip]
          linarith

/-! ### The theorems -/

/-- **Existence of the record of a set of crossings.** For every set of crossings of a similar tiling, some complete admissible record yields the tiling and places the tile to the upper left of a point before the tile to its lower right exactly at the crossings of the set. -/
theorem exists_record (hW : 0 < W) (hH : 0 < H) (h : IsSimilarTiling x (Rect.main W H) tl)
    {ori : Rect → Bool}
    (hori : ∀ T ∈ tl, (ori T = false → T.w = x * T.h) ∧ (ori T = true → T.h = x * T.w))
    {X : Set (ℝ × ℝ)} (hX : X ⊆ {q | IsCrossing tl q}) :
    ∃ (path : List Placement) (fresh : ℕ → ℝ), YieldsWith x W H tl ori path fresh ∧
      ∀ q, UpperFirst (tiles x W H fresh (initial W H) 0 path) q ↔ q ∈ X := by
  have hx : 0 < x := by linarith [h.one_le]
  have htl := h.toIsTiling
  obtain ⟨path, fresh, hy, hc⟩ := exists_chooses hW hH h hori hX
  have hord := Placing.order hx htl path _ _ (hy.placing h) hc
  refine ⟨path, fresh, hy, fun q => ⟨?_, fun hq => ?_⟩⟩
  · rintro ⟨U, V, hUq, hVq, hsub⟩
    exact (hord q U V hUq hVq).2 hsub
  · obtain ⟨U, hU, V, hV, hUq, hVq⟩ := (isCrossing_iff htl).mp (hX hq)
    have hperm := hy.2.2.1
    have hne : U ≠ V := by
      rintro rfl
      have := (htl.nondegenerate U hU).1
      linarith [hUq.1, hVq.1]
    rcases pair_sublist_total hne (hperm.mem_iff.mpr hU) (hperm.mem_iff.mpr hV) with h' | h'
    · exact absurd hq ((hord q U V hUq hVq).1 h')
    · exact ⟨U, V, hUq, hVq, h'⟩

/-- **The records of a tiling.** For every set of crossings of a similar tiling, with a choice of orientation for each tile that agrees with its shape, exactly one complete admissible record yields the tiling and places the tile to the upper left of a point before the tile to its lower right exactly at the crossings of the set. -/
theorem multiplicity (hW : 0 < W) (hH : 0 < H) (h : IsSimilarTiling x (Rect.main W H) tl)
    {ori : Rect → Bool}
    (hori : ∀ T ∈ tl, (ori T = false → T.w = x * T.h) ∧ (ori T = true → T.h = x * T.w))
    {X : Set (ℝ × ℝ)} (hX : X ⊆ {q | IsCrossing tl q}) :
    ∃! path : List Placement, ∃ fresh : ℕ → ℝ, YieldsWith x W H tl ori path fresh ∧
      ∀ q, UpperFirst (tiles x W H fresh (initial W H) 0 path) q ↔ q ∈ X := by
  obtain ⟨path, fresh, hy, hq⟩ := exists_record hW hH h hori hX
  refine ⟨path, ⟨fresh, hy, hq⟩, ?_⟩
  rintro path' ⟨fresh', hy', hq'⟩
  exact yieldsWith_unique h hy' hy fun q => (hq' q).trans (hq q).symm

open Classical in
/-- The set of points at which a record that yields the tiling places the tile to the upper left before the tile to the lower right. -/
noncomputable def upperFirstSet (x W H : ℝ) (tl : List Rect) (ori : Rect → Bool)
    (path : List Placement) : Set (ℝ × ℝ) :=
  if hp : Yields x W H tl ori path then
    {q | UpperFirst (tiles x W H (Classical.choose hp) (initial W H) 0 path) q}
  else ∅

theorem upperFirstSet_eq (h : IsSimilarTiling x (Rect.main W H) tl) {ori : Rect → Bool}
    {path : List Placement} {fresh : ℕ → ℝ} (hy : YieldsWith x W H tl ori path fresh) :
    upperFirstSet x W H tl ori path =
      {q | UpperFirst (tiles x W H fresh (initial W H) 0 path) q} := by
  have hp : Yields x W H tl ori path := ⟨fresh, hy⟩
  unfold upperFirstSet
  split
  · rw [YieldsWith.tiles_eq h (Classical.choose_spec ‹Yields x W H tl ori path›) hy]
  · exact absurd hp ‹_›

/-- The records that yield a similar tiling correspond to the sets of its crossings, a record corresponding to the set of crossings at which it places the tile to the upper left first. -/
theorem bijOn_upperFirstSet (hW : 0 < W) (hH : 0 < H) (h : IsSimilarTiling x (Rect.main W H) tl)
    {ori : Rect → Bool}
    (hori : ∀ T ∈ tl, (ori T = false → T.w = x * T.h) ∧ (ori T = true → T.h = x * T.w)) :
    Set.BijOn (upperFirstSet x W H tl ori) {path | Yields x W H tl ori path}
      (𝒫 {q | IsCrossing tl q}) := by
  have htl := h.toIsTiling
  refine ⟨?_, ?_, ?_⟩
  · rintro path ⟨fresh, hy⟩
    rw [upperFirstSet_eq h hy]
    rintro q ⟨U, V, hUq, hVq, hsub⟩
    have hperm := hy.2.2.1
    exact (isCrossing_iff htl).mpr ⟨U, hperm.mem_iff.mp (hsub.subset (by simp)), V,
      hperm.mem_iff.mp (hsub.subset (by simp)), hUq, hVq⟩
  · rintro path ⟨fresh, hy⟩ path' ⟨fresh', hy'⟩ heq
    rw [upperFirstSet_eq h hy, upperFirstSet_eq h hy'] at heq
    exact yieldsWith_unique h hy hy' fun q => Set.ext_iff.mp heq q
  · intro X hX
    obtain ⟨path, fresh, hy, hq⟩ := exists_record hW hH h hori hX
    refine ⟨path, ⟨fresh, hy⟩, ?_⟩
    rw [upperFirstSet_eq h hy]
    ext q
    exact hq q

/-- **The number of records.** A similar tiling with `k` crossings, with a choice of orientation for each tile that agrees with its shape, is yielded by exactly `2 ^ k` complete admissible records. -/
theorem ncard_records (hW : 0 < W) (hH : 0 < H) (h : IsSimilarTiling x (Rect.main W H) tl)
    {ori : Rect → Bool}
    (hori : ∀ T ∈ tl, (ori T = false → T.w = x * T.h) ∧ (ori T = true → T.h = x * T.w)) :
    {path | Yields x W H tl ori path}.ncard = 2 ^ {q | IsCrossing tl q}.ncard := by
  rw [(bijOn_upperFirstSet hW hH h hori).ncard_eq,
    Set.ncard_powerset _ (finite_crossings h.toIsTiling)]

end Rectiling
