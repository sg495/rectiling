-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Completeness
import Rectiling.Crossings

/-!
# The records that yield a tiling

A complete admissible record yields a tiling, with a choice of orientation for each tile, if for some free sides its constraints hold, its tiles are those of the tiling, and its placements have the chosen orientations.
Such a record places, at every stage, the tile at the anchor of the first tier whose floor does not extend to a point other than a crossing at which the tile to the upper left is placed before the tile to the lower right.
Hence two records that yield the same tiling and place the upper-left tile first at the same crossings are equal, and a tiling without crossings is yielded by at most one record.

The argument follows a record from an arbitrary stage and proves two facts by induction on the placements still to be made: the floor of a stale tier extends, and the tile at its end is placed before the tile to the upper left of the end; and a tile whose top-left corner is the end of a started floor is placed after a tile whose bottom-right corner is that end.
-/

namespace Rectiling

open scoped List

variable {x W H : ℝ} {tl : List Rect}

/-! ### Records that yield a tiling -/

/-- The record, with the given free sides, yields the tiling with the given orientations: it is complete admissible, its constraints hold, its tiles are those of the tiling, and each placement has the orientation chosen for its tile. -/
def YieldsWith (x W H : ℝ) (tl : List Rect) (ori : Rect → Bool) (path : List Placement)
    (fresh : ℕ → ℝ) : Prop :=
  Complete tl.length path ∧ Satisfies x fresh (initial W H) 0 path ∧
    (tiles x W H fresh (initial W H) 0 path).Perm tl ∧
    List.Forall₂ (fun mv T => mv.tall = ori T) path (tiles x W H fresh (initial W H) 0 path)

/-- The record yields the tiling with the given orientations, for some free sides. -/
def Yields (x W H : ℝ) (tl : List Rect) (ori : Rect → Bool) (path : List Placement) : Prop :=
  ∃ fresh, YieldsWith x W H tl ori path fresh

/-- The right end of the floor of a tier. -/
def GTier.tip (g : GTier) : ℝ × ℝ :=
  (g.ax + g.floor, g.ay)

/-- Every tile to the lower right of the point occurs in the list before every tile to its upper left. -/
def LowerFirst (tl ts : List Rect) (q : ℝ × ℝ) : Prop :=
  ∀ U ∈ tl, ∀ V ∈ tl, U.LowerRightOf q → V.UpperLeftOf q → [U, V] <+ ts

/-- A tile to the upper left of the point occurs in the list before a tile to its lower right. -/
def UpperFirst (ts : List Rect) (q : ℝ × ℝ) : Prop :=
  ∃ U V, U.LowerRightOf q ∧ V.UpperLeftOf q ∧ [V, U] <+ ts

theorem LowerFirst.cons {ts : List Rect} {q : ℝ × ℝ} (h : LowerFirst tl ts q) (a : Rect) :
    LowerFirst tl (a :: ts) q :=
  fun U hU V hV h1 h2 => (h U hU V hV h1 h2).cons a

/-! ### Auxiliary facts on placements and anchors -/

theorem Fit.eq_of_narrow_low {a b : Fit} (h1 : a.narrow = b.narrow) (h2 : a.low = b.low) :
    a = b := by
  cases a <;> cases b <;> first | rfl | simp [Fit.narrow, Fit.low] at h1 h2

/-- The anchors of a staircase with positive floors and walls proceed to the right and downwards. -/
theorem geom_pairwise {R top : ℝ} {l : List (Tier ℝ)} (hl : Positive l) :
    (geom R top l).Pairwise fun g₁ g₂ => g₁.ax + g₁.floor ≤ g₂.ax ∧ g₂.ay + g₂.wall ≤ g₁.ay := by
  induction l generalizing top with
  | nil => simp [geom]
  | cons t l ih =>
    have hl' : Positive l := fun u hu => hl u (by simp [hu])
    simp only [geom, List.pairwise_cons]
    refine ⟨fun g hg => ?_, ih hl'⟩
    obtain ⟨b1, -, -, b4, -, -⟩ := geom_bounds hl' g hg
    constructor <;> linarith

theorem gpreAfter_of_low {fit : Fit} (w : ℝ) (G : List GTier) (h : fit.low = true) :
    gpreAfter fit w G = G.map fun g => { g with stale := true } := by
  simp [gpreAfter, h]

theorem gpreAfter_concat {fit : Fit} (w : ℝ) (G : List GTier) (gp : GTier) (h : fit.low = false) :
    gpreAfter fit w (G ++ [gp]) =
      (G.map fun g => { g with stale := true }) ++
        [{ gp with stale := false, floor := gp.floor + w }] := by
  simp [gpreAfter, h]

theorem mem_gmidAfter_of_narrow {fit : Fit} (h : fit.narrow = true) (g : GTier) (w h' : ℝ) :
    ∃ g' ∈ gmidAfter fit g w h', g'.ax = g.ax + w ∧ g'.ay = g.ay ∧ g'.floor = g.floor - w ∧
      g'.started = true := by
  cases fit with
  | inside => exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, rfl, rfl, rfl⟩
  | fullHeight => exact ⟨_, List.mem_singleton_self _, rfl, rfl, rfl, rfl⟩
  | fullWidth => simp [Fit.narrow] at h
  | full => simp [Fit.narrow] at h

theorem mem_gpostAfter (fit : Fit) (h : ℝ) {G : List GTier} {g : GTier} (hg : g ∈ G) :
    ∃ g' ∈ gpostAfter fit h G, g'.ax = g.ax ∧ g'.ay = g.ay ∧ g'.floor = g.floor ∧
      g'.stale = g.stale ∧ g'.started = g.started := by
  unfold gpostAfter
  split
  · exact ⟨g, hg, rfl, rfl, rfl, rfl, rfl⟩
  · cases G with
    | nil => simp at hg
    | cons q rest =>
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨{ g with wall := g.wall + h }, by simp [onHead], rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨g, by simp [onHead, hg], rfl, rfl, rfl, rfl, rfl⟩

theorem tiles_cons {fresh : ℕ → ℝ} {s : List (Tier ℝ)} {k : ℕ} {mv : Placement}
    {rest : List Placement} {Q : Rect} (h : tileAt x W H s mv (fresh k) = some Q) :
    tiles x W H fresh s k (mv :: rest) =
      Q :: tiles x W H fresh (place (realAlgebra x) s mv (fresh k)) (nextIndex k mv) rest := by
  simp [tiles, h]

/-- The tiles of a placement for two free sides have the same bottom-left corner. -/
theorem tileAt_corner {s : List (Tier ℝ)} {mv : Placement} {a b : ℝ} {Q Q' : Rect}
    (ha : tileAt x W H s mv a = some Q) (hb : tileAt x W H s mv b = some Q') :
    Q.x = Q'.x ∧ Q.y = Q'.y := by
  unfold tileAt at ha hb
  cases hs : s[mv.tier]? with
  | none =>
    rw [hs] at ha
    simp at ha
  | some t =>
    rw [hs] at ha hb
    simp only [Option.map_some, Option.some.injEq] at ha hb
    subst ha hb
    exact ⟨rfl, rfl⟩

/-- The staircase after a placement depends on the free side only through the tile. -/
theorem place_eq_of_tileAt {s : List (Tier ℝ)} {mv : Placement} {a b : ℝ} {Q : Rect}
    (ha : tileAt x W H s mv a = some Q) (hb : tileAt x W H s mv b = some Q) :
    place (realAlgebra x) s mv a = place (realAlgebra x) s mv b := by
  unfold tileAt at ha hb
  unfold place
  cases hs : s[mv.tier]? with
  | none => rfl
  | some t =>
    rw [hs] at ha hb
    simp only [Option.map_some, Option.some.injEq] at ha hb
    rw [← hb] at ha
    simp only [Rect.mk.injEq, true_and] at ha
    have h1 : tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall a =
        tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall b := Prod.ext ha.1 ha.2
    simp only [h1]

/-! ### A record being placed -/

/-- A stage in the placing of a record whose tiles are tiles of the tiling: the staircase is positive, the placements still to be made obey the rules and their constraints hold, their tiles are tiles of the tiling, and every tile of the tiling whose interior meets the region is among them. -/
structure Placing (x W H : ℝ) (tl : List Rect) (fresh : ℕ → ℝ) (s : List (Tier ℝ)) (k : ℕ)
    (path : List Placement) : Prop where
  pos : Positive s
  allowed : Allowed (realAlgebra x) fresh s k path
  sat : Satisfies x fresh s k path
  sub : ∀ T ∈ tiles x W H fresh s k path, T ∈ tl
  full : ∀ Z ∈ tl, ¬Disjoint Z.inner (region W H s) → Z ∈ tiles x W H fresh s k path

/-- The next placement of a record being placed, in terms of the anchors: the tile `Q` is placed at the tier `g`, and `ts` are the tiles placed after it. -/
structure Head (W H : ℝ) (tl : List Rect) (fit : Fit) (Gpre : List GTier) (g : GTier)
    (Gpost : List GTier) (Q : Rect) (ts : List Rect) : Prop where
  around : Around W Gpre g Gpost
  hyp : StepHyp W Gpre g Gpost fit Q.w Q.h
  pairwise : (Gpre ++ g :: Gpost).Pairwise fun g₁ g₂ =>
    g₁.ax + g₁.floor ≤ g₂.ax ∧ g₂.ay + g₂.wall ≤ g₁.ay
  positive : ∀ g' ∈ Gpre ++ g :: Gpost, 0 < g'.floor ∧ 0 < g'.wall
  last : ∀ gp ∈ Gpre.getLast?, gp.ax + gp.floor = g.ax ∧ gp.ay = g.ay + g.wall
  top : Gpre = [] → g.ay + g.wall = H
  fresh : g.stale = false
  prev : fit.low = false → ∀ gp ∈ Gpre.getLast?, gp.started = false
  qx : Q.x = g.ax
  qy : Q.y = g.ay
  sub : ∀ T ∈ Q :: ts, T ∈ tl ∧ T.closed ⊆ unfilled W (Gpre ++ g :: Gpost)
  full : ∀ Z ∈ tl, ¬Disjoint Z.inner (unfilled W (Gpre ++ g :: Gpost)) → Z ∈ Q :: ts

/-- The next placement of a record being placed: its tier, its tile, the anchors after it, and the stage that follows. -/
theorem Placing.head (hx : 0 < x) {fresh : ℕ → ℝ} {s : List (Tier ℝ)} {k : ℕ} {mv : Placement}
    {rest : List Placement} (r : Placing x W H tl fresh s k (mv :: rest)) :
    ∃ (Gpre : List GTier) (g : GTier) (Gpost : List GTier) (Q : Rect),
      geom W H s = Gpre ++ g :: Gpost ∧ mv.tier = Gpre.length ∧
      tileAt x W H s mv (fresh k) = some Q ∧
      geom W H (place (realAlgebra x) s mv (fresh k)) =
        gpreAfter mv.fit Q.w Gpre ++ gmidAfter mv.fit g Q.w Q.h ++ gpostAfter mv.fit Q.h Gpost ∧
      Placing x W H tl fresh (place (realAlgebra x) s mv (fresh k)) (nextIndex k mv) rest ∧
      Head W H tl mv.fit Gpre g Gpost Q
        (tiles x W H fresh (place (realAlgebra x) s mv (fresh k)) (nextIndex k mv) rest) := by
  obtain ⟨hallow, hrest⟩ := r.allowed
  obtain ⟨hp, he⟩ := r.sat.head
  obtain ⟨pre, t, post, rfl, d⟩ := exists_stepData hx hallow hp he
  obtain ⟨hF, hW⟩ := not_doom hx fresh rest _ _ hrest r.sat.tail
  obtain ⟨hn, hl, hs'⟩ := d.positive_place r.pos hF hW
  obtain ⟨hw, hh, -⟩ := d.size
  have hT := tileAt_append x W H pre post t mv (fresh k) d.tier
  obtain ⟨T, hT', -, hb, -, hdis⟩ := step_region (W := W) (H := H) d.tier r.pos hw hh hn hl
  rw [hT] at hT'
  obtain rfl := Option.some.inj hT'
  have htiles := tiles_cons (rest := rest) hT
  have hall := (tiles_from hx W H fresh (mv :: rest) _ k r.pos r.allowed r.sat).1
  have ht := r.pos t (by simp)
  have hn' : if mv.fit.narrow then
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall (fresh k)).1 < t.floor
      else (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall (fresh k)).1 = t.floor := by
    split
    · exact hn ‹_›
    · exact tileSize_fst_of_not_narrow _ _ _ _ _ (by simpa using ‹¬mv.fit.narrow = true›)
  have hl' : if mv.fit.low then
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall (fresh k)).2 < t.wall
      else (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall (fresh k)).2 = t.wall := by
    split
    · exact hl ‹_›
    · exact tileSize_snd_of_not_low _ _ _ _ _ (by simpa using ‹¬mv.fit.low = true›)
  refine ⟨geom (W - (t.floor + sumFloor post)) H pre,
    ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale, t.started⟩,
    geom W (H - sumWall pre - t.wall) post, _, geom_split W H pre post t, by simpa using d.tier, hT,
    geom_place x W H pre post t mv (fresh k) d.tier, ⟨hs', hrest, r.sat.tail, ?_, ?_⟩, ?_⟩
  · intro T hT
    exact r.sub T (by rw [htiles]; exact List.mem_cons_of_mem _ hT)
  · intro Z hZ hnd
    have hZ' := r.full Z hZ fun hd => hnd (hd.mono_right hb)
    rw [htiles] at hZ'
    rcases List.mem_cons.mp hZ' with rfl | hZ'
    · exact absurd hdis hnd
    · exact hZ'
  · refine ⟨stepHyp_of_positive r.pos ht.1 ht.2 (by simp [Fit.narrow]) (by simp [Fit.low]),
      stepHyp_of_positive r.pos hw hh hn' hl', ?_, ?_, ?_, ?_, d.fresh, ?_, rfl, rfl, ?_, ?_⟩
    · rw [← geom_split]
      exact geom_pairwise r.pos
    · rw [← geom_split]
      intro g' hg'
      exact (geom_bounds r.pos g' hg').2.2.2.2
    · intro gp hgp
      rcases List.eq_nil_or_concat pre with rfl | ⟨l, p, rfl⟩
      · simp [geom] at hgp
      · rw [List.concat_eq_append, geom_concat] at hgp
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
          Option.some.injEq] at hgp
        subst hgp
        simp only [List.concat_eq_append, sumWall_append, sumWall_cons, sumWall_nil]
        constructor <;> ring
    · intro hnil
      have : pre = [] := by
        have := congrArg List.length hnil
        simpa using this
      subst this
      simp
    · intro hlow gp hgp
      rcases List.eq_nil_or_concat pre with rfl | ⟨l, p, rfl⟩
      · simp [geom] at hgp
      · rw [List.concat_eq_append, geom_concat] at hgp
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
          Option.some.injEq] at hgp
        subst hgp
        exact d.prev hlow p (by simp)
    · intro T hT
      rw [← htiles] at hT
      have := (hall T hT).2.2
      rw [region, geom_split] at this
      exact ⟨r.sub T hT, this⟩
    · intro Z hZ hnd
      rw [← htiles]
      refine r.full Z hZ ?_
      rw [region, geom_split]
      exact hnd

section HeadLemmas

variable {fit : Fit} {Gpre Gpost : List GTier} {g : GTier} {Q : Rect} {ts : List Rect}

theorem Head.mem (hd : Head W H tl fit Gpre g Gpost Q ts) : Q ∈ tl :=
  (hd.sub Q (by simp)).1

theorem Head.nondegenerate (hd : Head W H tl fit Gpre g Gpost Q ts) : Q.Nondegenerate :=
  ⟨hd.hyp.w_pos, hd.hyp.h_pos⟩

/-- The tiers before the tier of a placement: their floors extend, and at the end of each the tile to the lower right is placed first, provided that this holds of the stale tiers after the placement. -/
theorem Head.pre (htl : IsTiling (Rect.main W H) tl) (hd : Head W H tl fit Gpre g Gpost Q ts)
    (ih : ∀ g' ∈ gpreAfter fit Q.w Gpre, g'.stale = true →
      Ext tl (g'.ax + g'.floor) g'.ay ∧ LowerFirst tl ts g'.tip) :
    ∀ g' ∈ Gpre, Ext tl (g'.ax + g'.floor) g'.ay ∧ LowerFirst tl (Q :: ts) g'.tip := by
  intro g' hg'
  have hstale : { g' with stale := true } ∈ gpreAfter fit Q.w Gpre →
      Ext tl (g'.ax + g'.floor) g'.ay ∧ LowerFirst tl (Q :: ts) g'.tip := by
    intro hmem
    obtain ⟨hE, hL⟩ := ih _ hmem rfl
    exact ⟨hE, hL.cons Q⟩
  cases hlow : fit.low
  · rcases List.eq_nil_or_concat Gpre with rfl | ⟨G₁, gp, rfl⟩
    · simp at hg'
    · simp only [List.concat_eq_append] at hg' hd hstale
      rcases List.mem_append.mp hg' with hg₁ | hg₁
      · refine hstale ?_
        rw [gpreAfter_concat _ _ _ hlow]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨g', hg₁, rfl⟩)
      · obtain rfl : g' = gp := by simpa using hg₁
        -- the tile placed continues the floor
        obtain ⟨hl1, hl2⟩ := hd.last g' (by simp)
        have hQh : Q.h = g.wall := by
          have := hd.hyp.low
          simpa [hlow] using this
        obtain ⟨hQw, hQh'⟩ := hd.nondegenerate
        obtain ⟨hgf, hgw⟩ := hd.positive g' (by simp)
        have hle := hd.around.le_W
        have hfl := hd.around.w_pos
        have hwl := hd.around.h_pos
        have hqx := hd.qx
        have hqy := hd.qy
        refine ⟨⟨Q, hd.mem, by linarith, by linarith, by linarith⟩, ?_⟩
        intro U hU V hV hUq hVq
        obtain ⟨hUx, hUy⟩ := hUq
        obtain ⟨hVx, hVy⟩ := hVq
        simp only [GTier.tip] at hUx hUy hVx hVy
        have hUQ : U = Q :=
          htl.eq_of_corner hU hd.mem (Or.inl (by linarith)) (Or.inr (by linarith))
        obtain ⟨hVw, hVh⟩ := htl.nondegenerate V hV
        have hVmem : V ∈ Q :: ts := by
          apply hd.full V hV
          rw [Set.not_disjoint_iff]
          have m1 := le_max_left V.x g'.ax
          have m2 := le_max_right V.x g'.ax
          have m3 : max V.x g'.ax < g'.ax + g'.floor := max_lt (by linarith) (by linarith)
          have n1 := min_le_left (V.y + V.h) (g'.ay + g'.wall)
          have n2 := min_le_right (V.y + V.h) (g'.ay + g'.wall)
          have n3 : g'.ay < min (V.y + V.h) (g'.ay + g'.wall) := lt_min (by linarith) (by linarith)
          refine ⟨((max V.x g'.ax + (g'.ax + g'.floor)) / 2,
            (g'.ay + min (V.y + V.h) (g'.ay + g'.wall)) / 2), ?_, ?_⟩
          · rw [Rect.mem_inner]
            simp only
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
          · rw [mem_unfilled_append, mem_unfilled_append]
            refine Or.inl (Or.inr (mem_unfilled_cons.mpr (Or.inl ⟨?_, ?_, ?_, ?_⟩))) <;>
              simp only <;> linarith
        have hVne : V ≠ Q := by
          intro hVQ
          rw [hVQ] at hVy
          linarith
        rw [hUQ]
        exact pair_sublist_cons.mpr (Or.inr ⟨rfl, (List.mem_cons.mp hVmem).resolve_left hVne⟩)
  · refine hstale ?_
    rw [gpreAfter_of_low _ _ hlow]
    exact List.mem_map.mpr ⟨g', hg', rfl⟩

/-- A tile of the list whose top-left corner is the end of a started floor is preceded in the list by a tile whose bottom-right corner is that end. -/
def StartedOK (tl : List Rect) (G : List GTier) (ts : List Rect) : Prop :=
  ∀ g ∈ G, g.started = true → ∀ U ∈ ts, U.LowerRightOf g.tip →
    ∃ V ∈ tl, V.UpperLeftOf g.tip ∧ [V, U] <+ ts

/-- The property of started floors holds before a placement if it holds after it. -/
theorem Head.started (hd : Head W H tl fit Gpre g Gpost Q ts)
    (ih : StartedOK tl
      (gpreAfter fit Q.w Gpre ++ gmidAfter fit g Q.w Q.h ++ gpostAfter fit Q.h Gpost) ts) :
    StartedOK tl (Gpre ++ g :: Gpost) (Q :: ts) := by
  intro g' hg' hst U hU hUq
  obtain ⟨hUx, hUy⟩ := id hUq
  simp only [GTier.tip] at hUx hUy
  obtain ⟨hQw, hQh⟩ := hd.nondegenerate
  have hfl := hd.around.w_pos
  have hwl := hd.around.h_pos
  have hqx := hd.qx
  have hqy := hd.qy
  have key : ∀ g'' ∈ gpreAfter fit Q.w Gpre ++ gmidAfter fit g Q.w Q.h ++ gpostAfter fit Q.h Gpost,
      g''.started = true → g''.tip = g'.tip → U ≠ Q →
      ∃ V ∈ tl, V.UpperLeftOf g'.tip ∧ [V, U] <+ Q :: ts := by
    intro g'' hg'' hs'' htip hne
    obtain ⟨V, hV, hVq, hsub⟩ :=
      ih g'' hg'' hs'' U ((List.mem_cons.mp hU).resolve_left hne) (by rw [htip]; exact hUq)
    rw [htip] at hVq
    exact ⟨V, hV, hVq, hsub.cons Q⟩
  rcases List.mem_append.mp hg' with hpre | hmid
  · have hpa := hd.around.pre_above g' hpre
    cases hlow : fit.low
    · rcases List.eq_nil_or_concat Gpre with rfl | ⟨G₁, gp, rfl⟩
      · simp at hpre
      · simp only [List.concat_eq_append] at hpre hd key
        rcases List.mem_append.mp hpre with h₁ | h₁
        · obtain ⟨hl1, hl2⟩ := hd.last gp (by simp)
          have hrel := (List.pairwise_append.mp (List.pairwise_append.mp hd.pairwise).1).2.2 g' h₁
            gp (by simp)
          obtain ⟨hgf, hgw⟩ := hd.positive gp (by simp)
          refine key { g' with stale := true } ?_ hst rfl ?_
          · rw [gpreAfter_concat _ _ _ hlow]
            simp only [List.mem_append, List.mem_map]
            exact Or.inl (Or.inl (Or.inl ⟨g', h₁, rfl⟩))
          · intro hUQ
            rw [hUQ] at hUx
            linarith [hrel.1]
        · obtain rfl : g' = gp := by simpa using h₁
          have := hd.prev hlow g' (by simp)
          rw [this] at hst
          exact absurd hst (by simp)
    · refine key { g' with stale := true } ?_ hst rfl ?_
      · rw [gpreAfter_of_low _ _ hlow]
        simp only [List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨g', hpre, rfl⟩)
      · intro hUQ
        rw [hUQ] at hUy
        have : Q.h < g.wall := by
          have := hd.hyp.low
          simpa [hlow] using this
        linarith
  · rcases List.mem_cons.mp hmid with hgg | hpost
    · subst hgg
      have hne : U ≠ Q := by
        intro hUQ
        rw [hUQ] at hUx
        linarith
      cases hn : fit.narrow
      · have hw : Q.w = g'.floor := by
          have := hd.hyp.narrow
          simpa [hn] using this
        refine ⟨Q, hd.mem, ⟨?_, hqy⟩, pair_sublist_cons.mpr
          (Or.inr ⟨rfl, (List.mem_cons.mp hU).resolve_left hne⟩)⟩
        simp only [GTier.tip]
        linarith
      · obtain ⟨g'', hg'', e1, e2, e3, e4⟩ := mem_gmidAfter_of_narrow hn g' Q.w Q.h
        refine key g'' (by simp [hg'']) e4 ?_ hne
        simp only [GTier.tip, e1, e2, e3, Prod.mk.injEq, and_true]
        ring
    · obtain ⟨g'', hg'', e1, e2, e3, -, e5⟩ := mem_gpostAfter fit Q.h hpost
      have hpr := (hd.around.post_right g' hpost).1
      obtain ⟨hgf, hgw⟩ := hd.positive g' (by simp [hpost])
      refine key g'' (by simp [hg'']) (by rw [e5]; exact hst)
        (by simp only [GTier.tip, e1, e2, e3]) ?_
      intro hUQ
      rw [hUQ] at hUx
      linarith

/-- If the floor of the tier of a placement extends, its end is the top-left corner of a tile that is placed after a tile whose bottom-right corner is that end. -/
theorem Head.self (htl : IsTiling (Rect.main W H) tl) (hd : Head W H tl fit Gpre g Gpost Q ts)
    (ih : StartedOK tl (gmidAfter fit g Q.w Q.h) ts) (hE : Ext tl (g.ax + g.floor) g.ay) :
    UpperFirst (Q :: ts) g.tip := by
  obtain ⟨U, hU, hUy, hUx1, hUx2⟩ := hE
  obtain ⟨hUw, hUh⟩ := htl.nondegenerate U hU
  obtain ⟨-, hUW, -, -⟩ := htl.bounds hU
  obtain ⟨hQw, hQh⟩ := hd.nondegenerate
  have hfl := hd.around.w_pos
  have hwl := hd.around.h_pos
  have hqx := hd.qx
  have hqy := hd.qy
  obtain ⟨q, Gpost', rfl⟩ : ∃ q G, Gpost = q :: G := by
    cases Gpost with
    | nil =>
      have := hd.around.last rfl
      linarith
    | cons q G => exact ⟨q, G, rfl⟩
  obtain ⟨hq1, hq2⟩ := hd.around.head q (by simp)
  have hqw := (hd.around.post_right q (by simp)).2.2
  -- the tile that makes the floor extend is still to be placed
  have hUmem : U ∈ Q :: ts := by
    apply hd.full U hU
    rw [Set.not_disjoint_iff]
    have m1 := le_max_left U.y q.ay
    have m2 := le_max_right U.y q.ay
    have m3 : max U.y q.ay < g.ay := max_lt (by linarith) (by linarith)
    refine ⟨((g.ax + g.floor + (U.x + U.w)) / 2, (max U.y q.ay + g.ay) / 2), ?_, ?_⟩
    · rw [Rect.mem_inner]
      simp only
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rw [mem_unfilled_split]
      refine Or.inr (Or.inr (mem_unfilled_cons.mpr (Or.inl ⟨?_, ?_, ?_, ?_⟩))) <;>
        simp only <;> linarith
  have hUsub := (hd.sub U hUmem).2
  -- its left side is at the end of the floor
  have hUx : U.x = g.ax + g.floor := by
    refine le_antisymm hUx1 ?_
    by_contra hc
    have hc' := not_le.mp hc
    refine hd.around.not_mem (p := ((U.x + (g.ax + g.floor)) / 2, (U.y + (U.y + U.h)) / 2))
      ?_ (Or.inr ?_) ?_ (hUsub ?_)
    · simp only
      linarith
    · simp only
      linarith
    · simp only
      linarith
    · rw [Rect.mem_closed]
      simp only
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hne : U ≠ Q := by
    intro hUQ
    rw [hUQ] at hUx
    linarith
  have hUts := (List.mem_cons.mp hUmem).resolve_left hne
  have hUq : U.LowerRightOf g.tip := ⟨hUx, hUy⟩
  cases hn : fit.narrow
  · have hw : Q.w = g.floor := by
      have := hd.hyp.narrow
      simpa [hn] using this
    refine ⟨U, Q, hUq, ⟨?_, hqy⟩, pair_sublist_cons.mpr (Or.inr ⟨rfl, hUts⟩)⟩
    simp only [GTier.tip]
    linarith
  · obtain ⟨g'', hg'', e1, e2, e3, e4⟩ := mem_gmidAfter_of_narrow hn g Q.w Q.h
    have htip : g''.tip = g.tip := by
      simp only [GTier.tip, e1, e2, e3, Prod.mk.injEq, and_true]
      ring
    obtain ⟨V, -, hVq, hsub⟩ := ih g'' hg'' e4 U hUts (by rw [htip]; exact hUq)
    rw [htip] at hVq
    exact ⟨U, V, hUq, hVq, hsub.cons Q⟩

end HeadLemmas

/-! ### Stale tiers and started floors along a record -/

/-- The floor of a stale tier extends, and at its end the tile to the lower right is placed before the tile to the upper left. -/
theorem Placing.stale (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {fresh : ℕ → ℝ}
    (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), Placing x W H tl fresh s k path →
      ∀ g ∈ geom W H s, g.stale = true →
        Ext tl (g.ax + g.floor) g.ay ∧ LowerFirst tl (tiles x W H fresh s k path) g.tip := by
  induction path with
  | nil =>
    intro s k r g hg
    have hs := r.allowed
    simp only [Allowed] at hs
    subst hs
    simp [geom] at hg
  | cons mv rest ih =>
    intro s k r g hg hst
    obtain ⟨Gpre, g₀, Gpost, Q, hgeom, -, hQ, hafter, rtail, hd⟩ := r.head hx
    rw [tiles_cons hQ]
    rw [hgeom] at hg
    have ih' := ih _ _ rtail
    rw [hafter] at ih'
    rcases List.mem_append.mp hg with hg | hg
    · exact hd.pre htl (fun g' hg' => ih' g' (by simp [hg'])) g hg
    · rcases List.mem_cons.mp hg with hgg | hg
      · rw [hgg, hd.fresh] at hst
        exact absurd hst (by simp)
      · obtain ⟨g'', hg'', e1, e2, e3, e4, -⟩ := mem_gpostAfter mv.fit Q.h hg
        obtain ⟨hE, hL⟩ := ih' g'' (by simp [hg'']) (by rw [e4]; exact hst)
        have htip : g''.tip = g.tip := by simp only [GTier.tip, e1, e2, e3]
        rw [e1, e2, e3] at hE
        rw [htip] at hL
        exact ⟨hE, hL.cons Q⟩

/-- A tile still to be placed whose top-left corner is the end of a started floor is placed after a tile whose bottom-right corner is that end. -/
theorem Placing.started (hx : 0 < x) {fresh : ℕ → ℝ} (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), Placing x W H tl fresh s k path →
      StartedOK tl (geom W H s) (tiles x W H fresh s k path) := by
  induction path with
  | nil =>
    intro s k r g hg
    have hs := r.allowed
    simp only [Allowed] at hs
    subst hs
    simp [geom] at hg
  | cons mv rest ih =>
    intro s k r
    obtain ⟨Gpre, g₀, Gpost, Q, hgeom, -, hQ, hafter, rtail, hd⟩ := r.head hx
    rw [tiles_cons hQ, hgeom]
    have ih' := ih _ _ rtail
    rw [hafter] at ih'
    exact hd.started ih'

/-- A placement of a record being placed: the floors of the tiers before its tier extend, with the tile to the lower right of each end placed first, and if the floor of its tier extends then at its end the tile to the upper left is placed first. -/
theorem Placing.stage (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {fresh : ℕ → ℝ}
    {s : List (Tier ℝ)} {k : ℕ} {mv : Placement} {rest : List Placement}
    (r : Placing x W H tl fresh s k (mv :: rest)) :
    ∃ (Gpre : List GTier) (g : GTier) (Gpost : List GTier),
      geom W H s = Gpre ++ g :: Gpost ∧ mv.tier = Gpre.length ∧
      (∀ g' ∈ Gpre, Ext tl (g'.ax + g'.floor) g'.ay ∧
        LowerFirst tl (tiles x W H fresh s k (mv :: rest)) g'.tip) ∧
      (Ext tl (g.ax + g.floor) g.ay → UpperFirst (tiles x W H fresh s k (mv :: rest)) g.tip) := by
  obtain ⟨Gpre, g, Gpost, Q, hgeom, htier, hQ, hafter, rtail, hd⟩ := r.head hx
  have hS := Placing.stale hx htl rest _ _ rtail
  have hT := Placing.started hx rest _ _ rtail
  rw [hafter] at hS hT
  rw [tiles_cons hQ]
  exact ⟨Gpre, g, Gpost, hgeom, htier, hd.pre htl fun g' hg' => hS g' (by simp [hg']),
    hd.self htl fun g' hg' => hT g' (by simp [hg'])⟩

/-! ### The tier of each placement -/

/-- The floor ending at the point extends, and the point is not in the given set. -/
def XExt (tl : List Rect) (X : Set (ℝ × ℝ)) (q : ℝ × ℝ) : Prop :=
  Ext tl q.1 q.2 ∧ q ∉ X

theorem xExt_empty {q : ℝ × ℝ} : XExt tl ∅ q ↔ Ext tl q.1 q.2 := by
  simp [XExt]

/-- The index of the first tier that does not have the given property. -/
def FirstNot (P : GTier → Prop) (G : List GTier) (i : ℕ) : Prop :=
  (∃ g, G[i]? = some g ∧ ¬P g) ∧ ∀ j < i, ∀ g, G[j]? = some g → P g

theorem firstNot_split {P : GTier → Prop} {Gpre Gpost : List GTier} {g : GTier} :
    FirstNot P (Gpre ++ g :: Gpost) Gpre.length ↔ (∀ g' ∈ Gpre, P g') ∧ ¬P g := by
  constructor
  · rintro ⟨⟨g₀, h, hn⟩, hall⟩
    have : g = g₀ := by simpa using h
    subst this
    refine ⟨fun g' hg' => ?_, hn⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
    exact hall j hj _ (by rw [List.getElem?_append_left hj]; exact List.getElem?_eq_getElem hj)
  · rintro ⟨hpre, hn⟩
    refine ⟨⟨g, by simp, hn⟩, fun j hj g' hg' => hpre g' ?_⟩
    rw [List.getElem?_append_left hj] at hg'
    exact List.mem_of_getElem? hg'

theorem FirstNot.unique {P : GTier → Prop} {G : List GTier} {i j : ℕ} (hi : FirstNot P G i)
    (hj : FirstNot P G j) : i = j := by
  obtain ⟨⟨g, hg, hn⟩, hall⟩ := hi
  obtain ⟨⟨g', hg', hn'⟩, hall'⟩ := hj
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd (hall' i h g hg) hn
  · exact h
  · exact absurd (hall j h g' hg') hn'

/-- Every placement of the record is made at the first tier whose floor does not extend to a point outside the given set. -/
def Chooses (tl : List Rect) (X : Set (ℝ × ℝ)) (x W H : ℝ) (fresh : ℕ → ℝ) :
    List (Tier ℝ) → ℕ → List Placement → Prop
  | _, _, [] => True
  | s, k, mv :: rest =>
    FirstNot (fun g => XExt tl X g.tip) (geom W H s) mv.tier ∧
      Chooses tl X x W H fresh (place (realAlgebra x) s mv (fresh k)) (nextIndex k mv) rest

/-- A record being placed chooses its tiers by a set of points that contains the points at which the upper-left tile is placed first, and at each point of which some upper-left tile is not placed after some lower-right tile. -/
theorem Placing.chooses (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {X : Set (ℝ × ℝ)}
    {fresh : ℕ → ℝ} (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), Placing x W H tl fresh s k path →
      (∀ q, UpperFirst (tiles x W H fresh s k path) q → q ∈ X) →
      (∀ q ∈ X, ∃ U ∈ tl, ∃ V ∈ tl, U.LowerRightOf q ∧ V.UpperLeftOf q ∧
        ¬[U, V] <+ tiles x W H fresh s k path) →
      Chooses tl X x W H fresh s k path := by
  induction path with
  | nil =>
    intro s k _ _ _
    trivial
  | cons mv rest ih =>
    intro s k r h1 h2
    obtain ⟨Gpre, g, Gpost, hgeom, htier, hpre, hself⟩ := r.stage hx htl
    obtain ⟨_, _, _, Q, -, -, hQ, -, rtail, -⟩ := r.head hx
    rw [tiles_cons hQ] at h1 h2 hpre hself
    refine ⟨?_, ih _ _ rtail (fun q hq => h1 q ?_) fun q hq => ?_⟩
    · rw [hgeom, htier, firstNot_split]
      refine ⟨fun g' hg' => ⟨(hpre g' hg').1, fun hX => ?_⟩, fun hE => hE.2 (h1 _ (hself hE.1))⟩
      obtain ⟨U, hU, V, hV, hUq, hVq, hn⟩ := h2 _ hX
      exact hn ((hpre g' hg').2 U hU V hV hUq hVq)
    · obtain ⟨U, V, hU, hV, hsub⟩ := hq
      exact ⟨U, V, hU, hV, hsub.cons Q⟩
    · obtain ⟨U, hU, V, hV, hUq, hVq, hn⟩ := h2 q hq
      exact ⟨U, hU, V, hV, hUq, hVq, fun h => hn (h.cons Q)⟩

/-- Two records placed from the same staircase that choose their tiers by the same set and give their tiles the same orientations are equal. -/
theorem Placing.eq_of_chooses (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {X : Set (ℝ × ℝ)}
    {ori : Rect → Bool} {fresh fresh' : ℕ → ℝ} (path : List Placement) :
    ∀ (path' : List Placement) (s : List (Tier ℝ)) (k : ℕ), Placing x W H tl fresh s k path →
      Placing x W H tl fresh' s k path' → Chooses tl X x W H fresh s k path →
      Chooses tl X x W H fresh' s k path' →
      List.Forall₂ (fun mv T => mv.tall = ori T) path (tiles x W H fresh s k path) →
      List.Forall₂ (fun mv T => mv.tall = ori T) path' (tiles x W H fresh' s k path') →
      path = path' := by
  induction path with
  | nil =>
    intro path' s k r r' _ _ _ _
    have hs := r.allowed
    simp only [Allowed] at hs
    subst hs
    cases path' with
    | nil => rfl
    | cons mv' rest' =>
      obtain ⟨⟨⟨t, ht, -⟩, -⟩, -⟩ := r'.allowed
      simp at ht
  | cons mv rest ih =>
    intro path' s k r r' c c' o o'
    cases path' with
    | nil =>
      have hs := r'.allowed
      simp only [Allowed] at hs
      subst hs
      obtain ⟨⟨⟨t, ht, -⟩, -⟩, -⟩ := r.allowed
      simp at ht
    | cons mv' rest' =>
      obtain ⟨Gpre, g, Gpost, Q, hgeom, htier, hQ, -, rtail, hd⟩ := r.head hx
      obtain ⟨Gpre', g', Gpost', Q', hgeom', htier', hQ', -, rtail', hd'⟩ := r'.head hx
      obtain ⟨cf, ct⟩ := c
      obtain ⟨cf', ct'⟩ := c'
      have hti : mv.tier = mv'.tier := cf.unique cf'
      have hlen : Gpre.length = Gpre'.length := by rw [← htier, ← htier', hti]
      obtain ⟨rfl, hrest⟩ := List.append_inj (hgeom.symm.trans hgeom') hlen
      obtain ⟨rfl, rfl⟩ := List.cons.inj hrest
      have hQQ : Q = Q' := htl.eq_of_corner hd.mem hd'.mem (Or.inl (hd.qx.trans hd'.qx.symm))
        (Or.inl (hd.qy.trans hd'.qy.symm))
      subst hQQ
      rw [tiles_cons hQ] at o
      rw [tiles_cons hQ'] at o'
      obtain ⟨o1, o2⟩ := List.forall₂_cons.mp o
      obtain ⟨o1', o2'⟩ := List.forall₂_cons.mp o'
      have hfit : mv.fit = mv'.fit := by
        have a1 := hd.hyp.narrow
        have a2 := hd'.hyp.narrow
        have b1 := hd.hyp.low
        have b2 := hd'.hyp.low
        apply Fit.eq_of_narrow_low
        · cases h : mv.fit.narrow <;> cases h' : mv'.fit.narrow <;> simp [h, h'] at a1 a2 <;>
            first | rfl | linarith
        · cases h : mv.fit.low <;> cases h' : mv'.fit.low <;> simp [h, h'] at b1 b2 <;>
            first | rfl | linarith
      have hmv : mv = mv' := by
        cases mv
        cases mv'
        simp only [Placement.mk.injEq]
        exact ⟨hti, hfit, o1.trans o1'.symm⟩
      subst hmv
      have hplace := place_eq_of_tileAt hQ hQ'
      rw [← hplace] at rtail' ct' o2'
      rw [ih rest' _ _ rtail rtail' ct ct' o2 o2']

/-- The tiles of a record being placed do not depend on the free sides. -/
theorem Placing.tiles_eq (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl) {fresh fresh' : ℕ → ℝ}
    (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), Placing x W H tl fresh s k path →
      Placing x W H tl fresh' s k path →
      tiles x W H fresh s k path = tiles x W H fresh' s k path := by
  induction path with
  | nil =>
    intro s k _ _
    rfl
  | cons mv rest ih =>
    intro s k r r'
    obtain ⟨Gpre, g, Gpost, Q, -, -, hQ, -, rtail, hd⟩ := r.head hx
    obtain ⟨Gpre', g', Gpost', Q', -, -, hQ', -, rtail', hd'⟩ := r'.head hx
    obtain ⟨h1, h2⟩ := tileAt_corner hQ hQ'
    have hQQ : Q = Q' := htl.eq_of_corner hd.mem hd'.mem (Or.inl h1) (Or.inl h2)
    subst hQQ
    rw [tiles_cons hQ, tiles_cons hQ']
    have hplace := place_eq_of_tileAt hQ hQ'
    rw [← hplace] at rtail' ⊢
    rw [ih _ _ rtail rtail']

/-! ### The theorems -/

/-- A record that yields a tiling is a record being placed from the initial staircase. -/
theorem YieldsWith.placing (h : IsSimilarTiling x (Rect.main W H) tl) {ori : Rect → Bool}
    {path : List Placement} {fresh : ℕ → ℝ} (hy : YieldsWith x W H tl ori path fresh) :
    Placing x W H tl fresh (initial W H) 0 path := by
  obtain ⟨hc, hsat, hperm, -⟩ := hy
  have hx : 0 < x := by linarith [h.one_le]
  have hallowed := hc.allowed x W H fresh
  obtain ⟨hF, hW⟩ := not_doom hx fresh path _ _ hallowed hsat
  have hpos : Positive (initial W H) := by
    intro t ht
    simp only [initial, List.mem_singleton] at ht
    subst ht
    constructor
    · by_contra hc
      exact hF (Or.inr ⟨_, by simp [initial], not_lt.mp hc⟩)
    · by_contra hc
      exact hW (Or.inl (not_lt.mp hc))
  exact ⟨hpos, hallowed, hsat, fun T hT => hperm.mem_iff.mp hT, fun Z hZ _ => hperm.mem_iff.mpr hZ⟩

/-- The tiles of a record that yields a tiling, in the order of placement, do not depend on the free sides. -/
theorem YieldsWith.tiles_eq (h : IsSimilarTiling x (Rect.main W H) tl) {ori : Rect → Bool}
    {path : List Placement} {fresh fresh' : ℕ → ℝ} (hy : YieldsWith x W H tl ori path fresh)
    (hy' : YieldsWith x W H tl ori path fresh') :
    tiles x W H fresh (initial W H) 0 path = tiles x W H fresh' (initial W H) 0 path :=
  Placing.tiles_eq (by linarith [h.one_le]) h.toIsTiling path _ _ (hy.placing h) (hy'.placing h)

/-- A record that yields a tiling places, at every stage, the tile at the anchor of the first tier whose floor does not extend to a point other than those at which the tile to the upper left is placed before the tile to the lower right. -/
theorem YieldsWith.chooses (h : IsSimilarTiling x (Rect.main W H) tl) {ori : Rect → Bool}
    {path : List Placement} {fresh : ℕ → ℝ} (hy : YieldsWith x W H tl ori path fresh)
    {X : Set (ℝ × ℝ)}
    (hX : ∀ q, UpperFirst (tiles x W H fresh (initial W H) 0 path) q ↔ q ∈ X) :
    Chooses tl X x W H fresh (initial W H) 0 path := by
  have hx : 0 < x := by linarith [h.one_le]
  have htl := h.toIsTiling
  refine Placing.chooses hx htl path _ _ (hy.placing h) (fun q hq => (hX q).mp hq) ?_
  intro q hq
  obtain ⟨U, V, hUq, hVq, hsub⟩ := (hX q).mpr hq
  have hperm := hy.2.2.1
  have hnd : (tiles x W H fresh (initial W H) 0 path).Nodup := hperm.nodup_iff.mpr htl.nodup
  exact ⟨U, hperm.mem_iff.mp (hsub.subset (by simp)), V, hperm.mem_iff.mp (hsub.subset (by simp)),
    hUq, hVq, fun h' => pair_sublist_asymm hnd h' hsub⟩

/-- **The record of a tiling.** A complete admissible record that yields a similar tiling places, at every stage, the tile at the anchor of the first tier whose floor does not extend, provided that at every crossing the tile to the lower right is placed before the tile to the upper left. -/
theorem representative (h : IsSimilarTiling x (Rect.main W H) tl) {ori : Rect → Bool}
    {path : List Placement} {fresh : ℕ → ℝ} (hy : YieldsWith x W H tl ori path fresh)
    (hlow : ∀ q, IsCrossing tl q → LowerFirst tl (tiles x W H fresh (initial W H) 0 path) q) :
    Chooses tl ∅ x W H fresh (initial W H) 0 path := by
  have htl := h.toIsTiling
  refine hy.chooses h fun q => ⟨?_, fun hq => absurd hq (Set.notMem_empty q)⟩
  rintro ⟨U, V, hUq, hVq, hsub⟩
  exfalso
  have hperm := hy.2.2.1
  have hU : U ∈ tl := hperm.mem_iff.mp (hsub.subset (by simp))
  have hV : V ∈ tl := hperm.mem_iff.mp (hsub.subset (by simp))
  have hnd : (tiles x W H fresh (initial W H) 0 path).Nodup := hperm.nodup_iff.mpr htl.nodup
  exact pair_sublist_asymm hnd
    (hlow q ((isCrossing_iff htl).mpr ⟨U, hU, V, hV, hUq, hVq⟩) U hU V hV hUq hVq) hsub

/-- Two complete admissible records that yield the same similar tiling, with the same orientations, and place the tile to the upper left first at the same points, are equal. -/
theorem yieldsWith_unique (h : IsSimilarTiling x (Rect.main W H) tl) {ori : Rect → Bool}
    {path path' : List Placement} {fresh fresh' : ℕ → ℝ}
    (hy : YieldsWith x W H tl ori path fresh) (hy' : YieldsWith x W H tl ori path' fresh')
    (hX : ∀ q, UpperFirst (tiles x W H fresh (initial W H) 0 path) q ↔
      UpperFirst (tiles x W H fresh' (initial W H) 0 path') q) :
    path = path' :=
  Placing.eq_of_chooses (by linarith [h.one_le]) h.toIsTiling path path' _ _ (hy.placing h)
    (hy'.placing h)
    (hy.chooses h (X := {q | UpperFirst (tiles x W H fresh (initial W H) 0 path) q}) fun _ => Iff.rfl)
    (hy'.chooses h fun q => (hX q).symm) hy.2.2.2 hy'.2.2.2

/-- **Uniqueness of the record.** A similar tiling without crossings is yielded by at most one complete admissible record, for each choice of orientations. -/
theorem yields_unique_of_no_crossing (h : IsSimilarTiling x (Rect.main W H) tl)
    (hno : ∀ q, ¬IsCrossing tl q) {ori : Rect → Bool} {path path' : List Placement}
    (hy : Yields x W H tl ori path) (hy' : Yields x W H tl ori path') : path = path' := by
  obtain ⟨fresh, hy⟩ := hy
  obtain ⟨fresh', hy'⟩ := hy'
  have key : ∀ {p : List Placement} {f : ℕ → ℝ}, YieldsWith x W H tl ori p f →
      ∀ q, ¬UpperFirst (tiles x W H f (initial W H) 0 p) q := by
    rintro p f hp q ⟨U, V, hUq, hVq, hsub⟩
    have hperm := hp.2.2.1
    exact hno q ((isCrossing_iff h.toIsTiling).mpr ⟨U, hperm.mem_iff.mp (hsub.subset (by simp)), V,
      hperm.mem_iff.mp (hsub.subset (by simp)), hUq, hVq⟩)
  exact yieldsWith_unique h hy hy' fun q => ⟨fun hq => absurd hq (key hy q),
    fun hq => absurd hq (key hy' q)⟩

end Rectiling
