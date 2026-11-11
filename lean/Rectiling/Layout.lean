-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Geometry
import Rectiling.Staircase

/-!
# Geometric reading of the staircase

A staircase with real floors and walls, inside a main rectangle of given width and height, determines the position of every anchor, hence the region still to be filled and the rectangle occupied by each placed tile.
This module defines these and describes the effect of one placement on them.
-/

namespace Rectiling

/-- Sum of the floors. -/
def sumFloor (l : List (Tier ℝ)) : ℝ :=
  (l.map Tier.floor).sum

/-- Sum of the walls. -/
def sumWall (l : List (Tier ℝ)) : ℝ :=
  (l.map Tier.wall).sum

@[simp] theorem sumFloor_nil : sumFloor [] = 0 := rfl
@[simp] theorem sumWall_nil : sumWall [] = 0 := rfl
@[simp] theorem sumFloor_cons (t : Tier ℝ) (l : List (Tier ℝ)) :
    sumFloor (t :: l) = t.floor + sumFloor l := by simp [sumFloor]
@[simp] theorem sumWall_cons (t : Tier ℝ) (l : List (Tier ℝ)) :
    sumWall (t :: l) = t.wall + sumWall l := by simp [sumWall]
@[simp] theorem sumFloor_append (l₁ l₂ : List (Tier ℝ)) :
    sumFloor (l₁ ++ l₂) = sumFloor l₁ + sumFloor l₂ := by simp [sumFloor]
@[simp] theorem sumWall_append (l₁ l₂ : List (Tier ℝ)) :
    sumWall (l₁ ++ l₂) = sumWall l₁ + sumWall l₂ := by simp [sumWall]

/-- Positivity of every floor and wall. -/
def Positive (s : List (Tier ℝ)) : Prop :=
  ∀ t ∈ s, 0 < t.floor ∧ 0 < t.wall

theorem Positive.sumFloor_nonneg {s : List (Tier ℝ)} (h : Positive s) : 0 ≤ sumFloor s := by
  induction s with
  | nil => simp
  | cons t l ih =>
    have h1 := (h t (by simp)).1
    have h2 := ih fun u hu => h u (by simp [hu])
    simp only [sumFloor_cons]
    linarith

theorem Positive.sumWall_nonneg {s : List (Tier ℝ)} (h : Positive s) : 0 ≤ sumWall s := by
  induction s with
  | nil => simp
  | cons t l ih =>
    have h1 := (h t (by simp)).2
    have h2 := ih fun u hu => h u (by simp [hu])
    simp only [sumWall_cons]
    linarith

/-- Tier with the position of its anchor. -/
structure GTier where
  /-- Abscissa of the anchor. -/
  ax : ℝ
  /-- Ordinate of the anchor. -/
  ay : ℝ
  /-- Length of the floor. -/
  floor : ℝ
  /-- Height of the wall. -/
  wall : ℝ
  /-- Whether no tile can be placed until the floor grows. -/
  stale : Bool
  /-- Whether a tile already stands on the segment carrying the floor. -/
  started : Bool

/-- The tiers with their anchors, for a list of tiers whose floors end at abscissa `R` and whose walls start from ordinate `top`. -/
def geom (R top : ℝ) : List (Tier ℝ) → List GTier
  | [] => []
  | t :: rest =>
    ⟨R - (t.floor + sumFloor rest), top - t.wall, t.floor, t.wall, t.stale, t.started⟩ ::
      geom R (top - t.wall) rest

theorem geom_append (R top : ℝ) (l₁ l₂ : List (Tier ℝ)) :
    geom R top (l₁ ++ l₂) = geom (R - sumFloor l₂) top l₁ ++ geom R (top - sumWall l₁) l₂ := by
  induction l₁ generalizing top with
  | nil => simp [geom]
  | cons t l ih =>
    simp only [List.cons_append, geom, ih, sumFloor_append, sumWall_cons, List.cons.injEq,
      GTier.mk.injEq, and_true]
    refine ⟨by ring, ?_⟩
    rw [show top - t.wall - sumWall l = top - (t.wall + sumWall l) by ring]

/-- The tiers with their anchors, split around one tier. -/
theorem geom_split (W H : ℝ) (pre post : List (Tier ℝ)) (t : Tier ℝ) :
    geom W H (pre ++ t :: post) =
      geom (W - (t.floor + sumFloor post)) H pre ++
        ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale,
          t.started⟩ :: geom W (H - sumWall pre - t.wall) post := by
  rw [geom_append]
  simp [geom]

theorem geom_bounds {R top : ℝ} {l : List (Tier ℝ)} (hl : Positive l) :
    ∀ g ∈ geom R top l, R - sumFloor l ≤ g.ax ∧ g.ax + g.floor ≤ R ∧ top - sumWall l ≤ g.ay ∧
      g.ay + g.wall ≤ top ∧ 0 < g.floor ∧ 0 < g.wall := by
  induction l generalizing top with
  | nil => simp [geom]
  | cons t l ih =>
    have ht := hl t (by simp)
    have hl' : Positive l := fun u hu => hl u (by simp [hu])
    have h1 := hl'.sumFloor_nonneg
    have h2 := hl'.sumWall_nonneg
    intro g hg
    simp only [geom, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [sumFloor_cons, sumWall_cons]
      refine ⟨by linarith, by linarith, by linarith, by linarith, ht.1, ht.2⟩
    · obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ih hl' g hg
      simp only [sumFloor_cons, sumWall_cons]
      refine ⟨by linarith [ht.1], b2, by linarith, by linarith [ht.2], b5, b6⟩

/-! ### The region still to be filled -/

/-- Membership of a point in the horizontal strip of a tier, which extends from the anchor to the right side of the main rectangle and has the height of the wall. -/
def GTier.Mem (W : ℝ) (g : GTier) (p : ℝ × ℝ) : Prop :=
  g.ax ≤ p.1 ∧ p.1 ≤ W ∧ g.ay ≤ p.2 ∧ p.2 ≤ g.ay + g.wall

/-- The union of the strips of a list of tiers. -/
def unfilled (W : ℝ) (G : List GTier) : Set (ℝ × ℝ) :=
  {p | ∃ g ∈ G, g.Mem W p}

/-- The region still to be filled, for a staircase in a main rectangle of the given width and height. -/
def region (W H : ℝ) (s : List (Tier ℝ)) : Set (ℝ × ℝ) :=
  unfilled W (geom W H s)

theorem mem_unfilled_append {W : ℝ} {G₁ G₂ : List GTier} {p : ℝ × ℝ} :
    p ∈ unfilled W (G₁ ++ G₂) ↔ p ∈ unfilled W G₁ ∨ p ∈ unfilled W G₂ := by
  simp [unfilled, or_and_right, exists_or]

theorem mem_unfilled_cons {W : ℝ} {g : GTier} {G : List GTier} {p : ℝ × ℝ} :
    p ∈ unfilled W (g :: G) ↔ g.Mem W p ∨ p ∈ unfilled W G := by
  simp [unfilled]

@[simp]
theorem unfilled_nil (W : ℝ) : unfilled W [] = ∅ := by
  simp [unfilled]

theorem unfilled_congr {W : ℝ} {G G' : List GTier}
    (h : G.map (fun g => (g.ax, g.ay, g.wall)) = G'.map fun g => (g.ax, g.ay, g.wall)) :
    unfilled W G = unfilled W G' := by
  have key : ∀ G : List GTier, unfilled W G =
      {p | ∃ b ∈ G.map (fun g => (g.ax, g.ay, g.wall)),
        b.1 ≤ p.1 ∧ p.1 ≤ W ∧ b.2.1 ≤ p.2 ∧ p.2 ≤ b.2.1 + b.2.2} := by
    intro G
    ext p
    simp [unfilled, GTier.Mem]
  rw [key, key, h]

theorem region_initial (W H : ℝ) : region W H (initial W H) = (Rect.main W H).closed := by
  ext p
  simp [region, initial, geom, unfilled, GTier.Mem, Rect.mem_closed, Rect.main]

theorem region_nil (W H : ℝ) : region W H [] = ∅ := by
  simp [region, geom]

/-! ### The tile of a placement -/

/-- The rectangle occupied by the tile of a placement. -/
noncomputable def tileAt (x W H : ℝ) (s : List (Tier ℝ)) (mv : Placement) (side : ℝ) : Option Rect :=
  s[mv.tier]?.map fun t =>
    ⟨W - (t.floor + sumFloor (s.drop (mv.tier + 1))), H - sumWall (s.take mv.tier) - t.wall,
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1,
      (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2⟩

/-- The rectangles occupied by the tiles of a sequence of placements, in the order of placement. -/
noncomputable def tiles (x W H : ℝ) (fresh : ℕ → ℝ) : List (Tier ℝ) → ℕ → List Placement → List Rect
  | _, _, [] => []
  | s, k, mv :: rest =>
    (tileAt x W H s mv (fresh k)).toList ++
      tiles x W H fresh (place (realAlgebra x) s mv (fresh k)) (nextIndex k mv) rest

theorem tileAt_append (x W H : ℝ) (pre post : List (Tier ℝ)) (t : Tier ℝ) (mv : Placement)
    (side : ℝ) (h : mv.tier = pre.length) :
    tileAt x W H (pre ++ t :: post) mv side =
      some ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall,
        (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1,
        (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2⟩ := by
  simp [tileAt, h]

theorem tileSize_fst_of_not_narrow {L : Type} (A : Algebra L) {fit : Fit} (tall : Bool)
    (floor wall side : L) (h : fit.narrow = false) :
    (tileSize A fit tall floor wall side).1 = floor := by
  cases fit <;> cases tall <;> simp_all [tileSize, Fit.narrow]

theorem tileSize_snd_of_not_low {L : Type} (A : Algebra L) {fit : Fit} (tall : Bool)
    (floor wall side : L) (h : fit.low = false) :
    (tileSize A fit tall floor wall side).2 = wall := by
  cases fit <;> cases tall <;> simp_all [tileSize, Fit.low]

/-! ### The effect of a placement on the anchors -/

/-- The tiers before the tier of a placement, with their anchors, after the placement. -/
def gpreAfter (fit : Fit) (w : ℝ) (G : List GTier) : List GTier :=
  let stale := G.map fun g => { g with stale := true }
  if fit.low then stale
  else onLast (fun g => { g with stale := false, floor := g.floor + w }) stale

/-- The tiers that replace the tier of a placement, with their anchors. -/
def gmidAfter (fit : Fit) (g : GTier) (w h : ℝ) : List GTier :=
  match fit with
  | .inside =>
    [⟨g.ax, g.ay + h, w, g.wall - h, false, false⟩, ⟨g.ax + w, g.ay, g.floor - w, h, false, true⟩]
  | .fullHeight => [⟨g.ax + w, g.ay, g.floor - w, g.wall, false, true⟩]
  | .fullWidth => [⟨g.ax, g.ay + h, g.floor, g.wall - h, false, false⟩]
  | .full => []

/-- The tiers after the tier of a placement, with their anchors, after the placement. -/
def gpostAfter (fit : Fit) (h : ℝ) (G : List GTier) : List GTier :=
  if fit.narrow then G else onHead (fun g => { g with wall := g.wall + h }) G

theorem sumFloor_map_stale (l : List (Tier ℝ)) :
    sumFloor (l.map fun p => { p with stale := true }) = sumFloor l := by
  simp [sumFloor, Function.comp_def]

theorem sumWall_map_stale (l : List (Tier ℝ)) :
    sumWall (l.map fun p => { p with stale := true }) = sumWall l := by
  simp [sumWall, Function.comp_def]

theorem geom_map_stale (R top : ℝ) (l : List (Tier ℝ)) :
    geom R top (l.map fun p => { p with stale := true }) =
      (geom R top l).map fun g => { g with stale := true } := by
  induction l generalizing top with
  | nil => rfl
  | cons t l ih =>
    simp only [List.map_cons, geom, ih, sumFloor_map_stale]

theorem sumFloor_onLast (w : ℝ) (l : List (Tier ℝ)) (hl : l ≠ []) :
    sumFloor (onLast (fun p => { p with stale := false, floor := p.floor + w }) l) =
      sumFloor l + w := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩
  · exact absurd rfl hl
  · simp only [List.concat_eq_append, onLast_concat, sumFloor_append, sumFloor_cons, sumFloor_nil]
    ring

theorem sumWall_onLast (w : ℝ) (l : List (Tier ℝ)) :
    sumWall (onLast (fun p => { p with stale := false, floor := p.floor + w }) l) = sumWall l := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩ <;> simp

theorem geom_onLast (R top w : ℝ) (l : List (Tier ℝ)) :
    geom (R + w) top (onLast (fun p => { p with stale := false, floor := p.floor + w }) l) =
      onLast (fun g => { g with stale := false, floor := g.floor + w }) (geom R top l) := by
  induction l generalizing top with
  | nil => rfl
  | cons t l ih =>
    cases l with
    | nil =>
      simp only [onLast, geom, sumFloor_nil, add_zero, List.cons.injEq, GTier.mk.injEq, and_true]
      ring
    | cons u l =>
      have h := ih (top - t.wall)
      have hs := sumFloor_onLast w (u :: l) (by simp)
      simp only [onLast] at h hs ⊢
      rw [geom, h, hs]
      simp only [geom, onLast, List.cons.injEq, GTier.mk.injEq, and_true]
      ring

theorem sumFloor_onHead (h : ℝ) (l : List (Tier ℝ)) :
    sumFloor (onHead (fun q => { q with wall := q.wall + h }) l) = sumFloor l := by
  cases l <;> simp [onHead]

theorem geom_onHead (R top h : ℝ) (l : List (Tier ℝ)) :
    geom R (top + h) (onHead (fun q => { q with wall := q.wall + h }) l) =
      onHead (fun g => { g with wall := g.wall + h }) (geom R top l) := by
  cases l with
  | nil => rfl
  | cons q l =>
    simp only [onHead, geom, List.cons.injEq, GTier.mk.injEq, and_true]
    refine ⟨⟨trivial, by ring⟩, ?_⟩
    rw [show top + h - (q.wall + h) = top - q.wall by ring]

theorem sumWall_onHead (h : ℝ) (l : List (Tier ℝ)) (hl : l ≠ []) :
    sumWall (onHead (fun q => { q with wall := q.wall + h }) l) = sumWall l + h := by
  cases l with
  | nil => exact absurd rfl hl
  | cons q l =>
    simp only [onHead, sumWall_cons]
    ring

/-- The anchors after a placement, in terms of the anchors before it. -/
theorem geom_place (x W H : ℝ) (pre post : List (Tier ℝ)) (t : Tier ℝ) (mv : Placement) (side : ℝ)
    (hi : mv.tier = pre.length) :
    geom W H (place (realAlgebra x) (pre ++ t :: post) mv side) =
      gpreAfter mv.fit (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1
          (geom (W - (t.floor + sumFloor post)) H pre) ++
        gmidAfter mv.fit
          ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale,
            t.started⟩
          (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1
          (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 ++
        gpostAfter mv.fit (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2
          (geom W (H - sumWall pre - t.wall) post) := by
  rw [place_append _ pre post t mv side hi]
  have hw := tileSize_fst_of_not_narrow (realAlgebra x) mv.tall t.floor t.wall side (fit := mv.fit)
  have hh := tileSize_snd_of_not_low (realAlgebra x) mv.tall t.floor t.wall side (fit := mv.fit)
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 = w at hw ⊢
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 = h at hh ⊢
  -- sums of the new tiers
  have hpostF : sumFloor (postAfter (realAlgebra x) mv.fit h post) = sumFloor post := by
    unfold postAfter
    split
    · rfl
    · exact sumFloor_onHead h post
  have hpreW : sumWall (preAfter (realAlgebra x) mv.fit w pre) = sumWall pre := by
    unfold preAfter
    split
    · exact sumWall_map_stale pre
    · exact (sumWall_onLast w _).trans (sumWall_map_stale pre)
  rw [geom_append, geom_append, sumWall_append, hpostF, hpreW]
  -- the three parts
  have hpre : geom (W - sumFloor post - sumFloor (midAfter (realAlgebra x) mv.fit t w h)) H
      (preAfter (realAlgebra x) mv.fit w pre) =
      gpreAfter mv.fit w (geom (W - (t.floor + sumFloor post)) H pre) := by
    unfold preAfter gpreAfter
    cases hfit : mv.fit
    · simp only [Fit.low, ite_true, midAfter, realAlgebra, sumFloor_cons, sumFloor_nil,
        geom_map_stale]
      rw [show W - sumFloor post - (w + (t.floor - w + 0)) = W - (t.floor + sumFloor post) by ring]
    · simp only [Fit.low, Bool.false_eq_true, ite_false, midAfter, realAlgebra, sumFloor_cons,
        sumFloor_nil]
      rw [show W - sumFloor post - (t.floor - w + 0) = W - (t.floor + sumFloor post) + w by ring,
        geom_onLast, geom_map_stale]
    · simp only [Fit.low, ite_true, midAfter, realAlgebra, sumFloor_cons, sumFloor_nil,
        geom_map_stale]
      rw [show W - sumFloor post - (t.floor + 0) = W - (t.floor + sumFloor post) by ring]
    · have hw' := hw (by simp [hfit, Fit.narrow])
      simp only [Fit.low, Bool.false_eq_true, ite_false, midAfter, realAlgebra, sumFloor_nil]
      rw [show W - sumFloor post - 0 = W - (t.floor + sumFloor post) + w by rw [hw']; ring,
        geom_onLast, geom_map_stale]
  have hmid : geom (W - sumFloor post) (H - sumWall pre) (midAfter (realAlgebra x) mv.fit t w h) =
      gmidAfter mv.fit ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall,
        t.stale, t.started⟩ w h := by
    cases hfit : mv.fit <;>
      simp only [midAfter, gmidAfter, geom, realAlgebra, sumFloor_cons, sumFloor_nil,
        List.cons.injEq, GTier.mk.injEq, and_true] <;>
      (repeat' apply And.intro) <;> ring
  have hpost : geom W (H - (sumWall pre + sumWall (midAfter (realAlgebra x) mv.fit t w h)))
      (postAfter (realAlgebra x) mv.fit h post) =
      gpostAfter mv.fit h (geom W (H - sumWall pre - t.wall) post) := by
    unfold postAfter gpostAfter
    cases hfit : mv.fit
    · simp only [Fit.narrow, ite_true, midAfter, realAlgebra, sumWall_cons, sumWall_nil]
      rw [show H - (sumWall pre + (t.wall - h + (h + 0))) = H - sumWall pre - t.wall by ring]
    · simp only [Fit.narrow, ite_true, midAfter, sumWall_cons, sumWall_nil]
      rw [show H - (sumWall pre + (t.wall + 0)) = H - sumWall pre - t.wall by ring]
    · simp only [Fit.narrow, Bool.false_eq_true, ite_false, midAfter, realAlgebra, sumWall_cons,
        sumWall_nil]
      rw [show H - (sumWall pre + (t.wall - h + 0)) = H - sumWall pre - t.wall + h by ring,
        geom_onHead]
    · have hh' := hh (by simp [hfit, Fit.low])
      simp only [Fit.narrow, Bool.false_eq_true, ite_false, midAfter, realAlgebra, sumWall_nil]
      rw [show H - (sumWall pre + 0) = H - sumWall pre - t.wall + h by rw [hh']; ring, geom_onHead]
  rw [hpre, hmid, hpost]

end Rectiling
