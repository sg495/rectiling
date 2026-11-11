-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Extension

/-!
# Completeness of the staircase

Every tiling of the `W × H` rectangle by `n` rectangles of proportion `x ≥ 1` is the list of tiles of a complete admissible placement sequence, for free sides that satisfy the emitted constraints.
When the main rectangle is a square, the tiling or its transpose is obtained from a sequence whose first tile is wide.
-/

namespace Rectiling

/-! ### Auxiliary facts on lists and anchors -/

theorem geom_concat (R top : ℝ) (l : List (Tier ℝ)) (p : Tier ℝ) :
    geom R top (l ++ [p]) = geom (R - p.floor) top l ++
      [⟨R - p.floor, top - sumWall l - p.wall, p.floor, p.wall, p.stale, p.started⟩] := by
  rw [geom_append]
  simp [geom]

@[simp]
theorem length_geom (R top : ℝ) (l : List (Tier ℝ)) : (geom R top l).length = l.length := by
  induction l generalizing top with
  | nil => rfl
  | cons t l ih => simp [geom, ih]

theorem exists_first_not {α : Type} (P : α → Prop) :
    ∀ l : List α, (∃ a ∈ l, ¬P a) → ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ (∀ b ∈ l₁, P b) ∧ ¬P a
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : P a
    · have h' : ∃ b ∈ l, ¬P b := by
        obtain ⟨b, hb, hnb⟩ := h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact absurd ha hnb
        · exact ⟨b, hb, hnb⟩
      obtain ⟨l₁, b, l₂, rfl, h1, h2⟩ := exists_first_not P l h'
      refine ⟨a :: l₁, b, l₂, rfl, ?_, h2⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ha
      · exact h1 c hc
    · exact ⟨[], a, l, rfl, by simp, ha⟩

variable {W H : ℝ} {tl : List Rect}

/-- The first tier whose floor does not extend. -/
theorem exists_first_tier (htl : IsTiling (Rect.main W H) tl) {s : List (Tier ℝ)} (hs : s ≠ []) :
    ∃ pre t post, s = pre ++ t :: post ∧
      (∀ g' ∈ geom (W - (t.floor + sumFloor post)) H pre, Ext tl (g'.ax + g'.floor) g'.ay) ∧
      ¬Ext tl (W - (t.floor + sumFloor post) + t.floor) (H - sumWall pre - t.wall) := by
  have hex : ∃ g ∈ geom W H s, ¬Ext tl (g.ax + g.floor) g.ay := by
    rcases List.eq_nil_or_concat s with rfl | ⟨s', p, rfl⟩
    · exact absurd rfl hs
    · rw [List.concat_eq_append, geom_concat]
      refine ⟨⟨W - p.floor, H - sumWall s' - p.wall, p.floor, p.wall, p.stale, p.started⟩,
        by simp, ?_⟩
      rintro ⟨T, hT, -, -, h3⟩
      have hT' := htl.subset hT (a := (T.x + T.w, T.y)) (by
        rw [Rect.mem_closed]
        have := htl.nondegenerate T hT
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith [this.1, this.2])
      rw [Rect.mem_closed] at hT'
      simp only [Rect.main, zero_add] at hT' h3
      linarith [hT'.2.1]
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

/-- The size of a tile of proportion `x` that fits its tier, as computed by the placement. -/
theorem tileSize_of_tile {x : ℝ} (hx : 0 < x) {fit : Fit} {tall : Bool} {floor wall side w h : ℝ}
    (hwide : tall = false → w = x * h) (htall : tall = true → h = x * w)
    (hn : fit.narrow = false → w = floor) (hl : fit.low = false → h = wall)
    (hside : fit = .inside → side = if tall then w else h) :
    tileSize (realAlgebra x) fit tall floor wall side = (w, h) := by
  have hx' : x ≠ 0 := hx.ne'
  cases fit <;> cases tall <;>
    simp only [tileSize, realAlgebra, Fit.narrow, Fit.low, forall_const, Bool.false_eq_true,
      ite_false, ite_true, IsEmpty.forall_iff, reduceCtorEq, Prod.mk.injEq] at *
  · exact ⟨by rw [hside, hwide], hside⟩
  · exact ⟨hside, by rw [hside, htall]⟩
  · exact ⟨by rw [← hl, hwide], hl.symm⟩
  · refine ⟨?_, hl.symm⟩
    rw [← hl, htall]
    field_simp
  · refine ⟨hn.symm, ?_⟩
    rw [← hn, hwide]
    field_simp
  · exact ⟨hn.symm, by rw [← hn, htall]⟩
  · exact ⟨hn.symm, hl.symm⟩
  · exact ⟨hn.symm, hl.symm⟩

theorem tiles_congr {x : ℝ} {f g : ℕ → ℝ} (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), (∀ j, k ≤ j → f j = g j) →
      tiles x W H f s k path = tiles x W H g s k path := by
  induction path with
  | nil => intro s k _; rfl
  | cons mv rest ih =>
    intro s k hfg
    have hk := hfg k (le_refl k)
    have := ih (place (realAlgebra x) s mv (g k)) (nextIndex k mv)
      fun j hj => hfg j ((le_nextIndex k mv).trans hj)
    simp only [tiles, hk, this]

/-! ### One step of the construction -/

/-- Invariant of the construction: floors and walls are positive, and the invariant on the anchors holds. -/
structure CInv (tl : List Rect) (W H : ℝ) (s : List (Tier ℝ)) (placed rem : List Rect) : Prop where
  pos : Positive s
  ginv : GInv tl W H (geom W H s) placed rem

/-- One step of the construction: a placement that obeys the rules, whose tile is one of the remaining tiles of the tiling and whose constraints hold, and after which the invariant holds. -/
theorem CInv.step {x : ℝ} (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl)
    (hprop : ∀ T ∈ tl, T.HasProportion x) {s : List (Tier ℝ)} {placed rem : List Rect}
    (inv : CInv tl W H s placed rem) (hs : s ≠ []) :
    ∃ (mv : Placement) (side : ℝ) (Q : Rect) (rem' : List Rect), rem.Perm (Q :: rem') ∧
      (mv.tall = false ↔ Q.w = x * Q.h) ∧
      ∀ side', (mv.fit = .inside → side' = side) →
        Allows s mv ∧ tileAt x W H s mv side' = some Q ∧ (∀ c ∈ positiveAt s mv side', 0 < c) ∧
          (∀ e ∈ equationAt (realAlgebra x) s mv, e = 0) ∧
          CInv tl W H (place (realAlgebra x) s mv side') (placed ++ [Q]) rem' := by
  obtain ⟨pre, t, post, rfl, hprevE, hE⟩ := exists_first_tier htl hs
  have ht := inv.pos t (by simp)
  have A : Around W (geom (W - (t.floor + sumFloor post)) H pre)
      ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor, t.wall, t.stale,
        t.started⟩ (geom W (H - sumWall pre - t.wall) post) :=
    stepHyp_of_positive inv.pos ht.1 ht.2 (by simp [Fit.narrow]) (by simp [Fit.low])
  have ginv := inv.ginv
  rw [geom_split] at ginv
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
  obtain ⟨Q, rem', hperm, hQnd, hQx, hQy, hw, hh, hG⟩ := ginv.step htl A hprevE hE hlast htop
  simp only at hQx hQy hw hh
  have hQtl : Q ∈ tl := inv.ginv.perm.mem_iff.mpr
    (List.mem_append_right _ (hperm.mem_iff.mpr (by simp)))
  obtain ⟨tall, htall1, htall2⟩ : ∃ tall : Bool, (tall = false ↔ Q.w = x * Q.h) ∧
      (tall = true → Q.h = x * Q.w) := by
    by_cases hwide : Q.w = x * Q.h
    · exact ⟨false, by simp [hwide], by simp⟩
    · exact ⟨true, by simp [hwide], fun _ => (hprop Q hQtl).resolve_left hwide⟩
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
  refine ⟨⟨pre.length, fit, tall⟩, if tall then Q.w else Q.h, Q, rem', hperm, htall1, ?_⟩
  intro side' hside
  have hsize : tileSize (realAlgebra x) fit tall t.floor t.wall side' = (Q.w, Q.h) :=
    tileSize_of_tile hx (fun h => htall1.mp h) htall2 hn2 hl2 hside
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [allows_append rfl]
    constructor
    · by_contra hc
      have hst : t.stale = true := by simpa using hc
      have hflag := ginv.flags ⟨W - (t.floor + sumFloor post), H - sumWall pre - t.wall, t.floor,
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
        exact (ginv.flags _ (List.mem_append_left _ hmem)).2 hst (hprevE _ hmem)
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
      rw [← hn2 rfl, ← hl2 rfl, htall1.mp rfl]
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

/-! ### The construction -/

/-- The orientation of each placement records which side of its tile is the long one. -/
def Oriented (x : ℝ) (path : List Placement) (ts : List Rect) : Prop :=
  List.Forall₂ (fun mv T => mv.tall = false ↔ T.w = x * T.h) path ts

/-- From any state satisfying the invariant, the remaining tiles are produced by a sequence of placements that obeys the rules, empties the staircase, and whose constraints hold. -/
theorem complete_from {x : ℝ} (hx : 0 < x) (htl : IsTiling (Rect.main W H) tl)
    (hprop : ∀ T ∈ tl, T.HasProportion x) :
    ∀ (n : ℕ) (s : List (Tier ℝ)) (k : ℕ) (placed rem : List Rect), rem.length = n →
      CInv tl W H s placed rem →
      ∃ (path : List Placement) (fresh : ℕ → ℝ), Allowed (realAlgebra x) fresh s k path ∧
        Satisfies x fresh s k path ∧ (tiles x W H fresh s k path).Perm rem ∧
        Oriented x path (tiles x W H fresh s k path) := by
  intro n
  induction n with
  | zero =>
    intro s k placed rem hlen inv
    have hrem : rem = [] := List.length_eq_zero_iff.mp hlen
    subst hrem
    have hs : s = [] := by
      by_contra hs
      obtain ⟨mv, side, Q, rem', hperm, -⟩ := inv.step hx htl hprop hs
      simpa using hperm.length_eq
    subst hs
    exact ⟨[], fun _ => 0, rfl, ⟨by simp [positives], by simp [equations]⟩, by simp [tiles],
      List.Forall₂.nil⟩
  | succ n ih =>
    intro s k placed rem hlen inv
    have hs : s ≠ [] := by
      rintro rfl
      obtain ⟨T, rest, rfl⟩ := List.exists_cons_of_ne_nil (l := rem) (by
        intro h
        simp [h] at hlen)
      have hT : T ∈ tl := inv.ginv.perm.mem_iff.mpr (by simp)
      have hnd := htl.nondegenerate T hT
      have hsub := inv.ginv.rem_subset T (by simp)
      have hp : ((T.x + T.w / 2, T.y + T.h / 2) : ℝ × ℝ) ∈ T.inner := by
        rw [Rect.mem_inner]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith [hnd.1, hnd.2]
      have := hsub hp
      simp [geom] at this
    obtain ⟨mv, side, Q, rem', hperm, hori, hstep⟩ := inv.step hx htl hprop hs
    have hlen' : rem'.length = n := by
      have := hperm.length_eq
      simp only [List.length_cons] at this
      omega
    obtain ⟨-, -, -, -, hinv'⟩ := hstep side fun _ => rfl
    obtain ⟨path', fresh', a1, a2, a3, a4⟩ :=
      ih (place (realAlgebra x) s mv side) (nextIndex k mv) (placed ++ [Q]) rem' hlen' hinv'
    have key : ∀ fresh : ℕ → ℝ, (mv.fit = .inside → fresh k = side) →
        place (realAlgebra x) s mv (fresh k) = place (realAlgebra x) s mv side →
        (∀ j, nextIndex k mv ≤ j → fresh j = fresh' j) →
        ∃ (path : List Placement) (fresh : ℕ → ℝ), Allowed (realAlgebra x) fresh s k path ∧
          Satisfies x fresh s k path ∧ (tiles x W H fresh s k path).Perm rem ∧
          Oriented x path (tiles x W H fresh s k path) := by
      intro fresh hside hplace hagree
      obtain ⟨b1, b2, b3, b4, -⟩ := hstep (fresh k) hside
      obtain ⟨c1, c2, c3⟩ := run_congr (realAlgebra x) path' (place (realAlgebra x) s mv side)
        (nextIndex k mv) fun j hj _ => hagree j hj
      have c4 := tiles_congr (x := x) (W := W) (H := H) path' (place (realAlgebra x) s mv side)
        (nextIndex k mv) hagree
      refine ⟨mv :: path', fresh, ⟨b1, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
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
        exact List.Forall₂.cons hori a4
    by_cases hfit : mv.fit = .inside
    · refine key (Function.update fresh' k side) (fun _ => by simp) (by simp) ?_
      intro j hj
      have : j ≠ k := by
        simp only [nextIndex, hfit, ite_true] at hj
        omega
      simp [Function.update_of_ne this]
    · exact key fresh' (fun h => absurd h hfit) (place_side _ s mv _ _ hfit) fun _ _ => rfl

/-! ### Admissibility of the constructed sequence -/

/-- A sequence that obeys the rules and empties the staircase is admissible: the bound on the number of remaining tiles holds of itself. -/
theorem Allowed.completeFrom {f : ℕ → Unit} (path : List Placement) :
    ∀ (s : List (Tier Unit)) (k : ℕ), Allowed unitAlgebra f s k path →
      s.length ≤ path.length ∧ CompleteFrom s path.length path := by
  induction path with
  | nil =>
    intro s k h
    simp only [Allowed] at h
    subst h
    exact ⟨le_refl _, rfl⟩
  | cons mv rest ih =>
    intro s k h
    obtain ⟨hallow, hrest⟩ := h
    obtain ⟨⟨t, ht, -⟩, -⟩ := id hallow
    have hlen := length_place unitAlgebra () ht
    obtain ⟨h1, h2⟩ := ih (place unitAlgebra s mv ()) (nextIndex k mv) hrest
    rw [hlen] at h1
    have hge : s.length ≤ tiersAfter s.length mv.fit + 1 := by
      cases mv.fit <;> simp only [tiersAfter] <;> omega
    refine ⟨by simp only [List.length_cons]; omega, ⟨hallow, by simp, ?_, ?_⟩, ?_⟩
    · simpa using h1
    · intro h0
      have hnil : place unitAlgebra s mv () = [] := List.length_eq_zero_iff.mp (hlen.trans h0)
      cases rest with
      | nil => rfl
      | cons mv' rest' =>
        have hbad : Allows (place unitAlgebra s mv ()) mv' := hrest.1
        rw [hnil] at hbad
        obtain ⟨⟨t', ht', -⟩, -⟩ := hbad
        simp at ht'
    · simpa using h2

/-! ### The theorems -/

/-- **Completeness.** Every tiling of the `W × H` rectangle by rectangles of proportion `x ≥ 1` is, up to the order of the tiles, the list of tiles of a complete admissible placement sequence, for free sides that satisfy the emitted equations and positivity constraints; the orientation of each placement records which side of its tile is the long one. -/
theorem completeness {x : ℝ} (hW : 0 < W) (hH : 0 < H)
    (h : IsSimilarTiling x (Rect.main W H) tl) :
    ∃ (path : List Placement) (fresh : ℕ → ℝ), Complete tl.length path ∧
      Satisfies x fresh (initial W H) 0 path ∧
      (tiles x W H fresh (initial W H) 0 path).Perm tl ∧
      Oriented x path (tiles x W H fresh (initial W H) 0 path) := by
  have hx : 0 < x := by linarith [h.one_le]
  have htl := h.toIsTiling
  have inv : CInv tl W H (initial W H) [] tl := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simp [FlagsOK, initial, geom]
  obtain ⟨path, fresh, a1, a2, a3, a4⟩ :=
    complete_from hx htl h.proportion tl.length (initial W H) 0 [] tl rfl inv
  have hlen : path.length = tl.length := a4.length_eq.trans a3.length_eq
  have hunit := (allowed_map (Algebra.isHom_unit (realAlgebra x)) fresh (initial W H) 0 path).mpr a1
  have hcomp := (Allowed.completeFrom path _ 0 hunit).2
  rw [hlen] at hcomp
  exact ⟨path, fresh, hcomp, a2, a3, a4⟩

/-- The first tile of a complete admissible sequence has its bottom-left corner at the origin. -/
theorem head_tile_origin {x : ℝ} {n : ℕ} {mv : Placement} {rest : List Placement}
    (hpath : Complete n (mv :: rest)) (fresh : ℕ → ℝ) :
    ∃ T ts, tiles x W H fresh (initial W H) 0 (mv :: rest) = T :: ts ∧ T.x = 0 ∧ T.y = 0 := by
  obtain ⟨⟨⟨⟨t, ht, -⟩, -⟩, -⟩, -⟩ := hpath
  have htier : mv.tier = 0 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ht
    simp only [initial, List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hlt
    exact hlt
  have := tileAt_append x W H [] [] ⟨W, H, false, false⟩ mv (fresh 0) (by simpa using htier)
  have key : ∃ T, tileAt x W H (initial W H) mv (fresh 0) = some T ∧ T.x = 0 ∧ T.y = 0 :=
    ⟨_, this, by simp, by simp⟩
  obtain ⟨T, hT, h1, h2⟩ := key
  exact ⟨T, _, by simp only [tiles, hT]; rfl, h1, h2⟩

/-- **Completeness for a square.** Every tiling of a square by rectangles of proportion `x ≥ 1` is obtained, possibly after transposition, from a complete admissible placement sequence whose first tile is wide. -/
theorem completeness_square {x : ℝ} (hW : 0 < W) (h : IsSimilarTiling x (Rect.main W W) tl) :
    ∃ (path : List Placement) (fresh : ℕ → ℝ), Complete tl.length path ∧ FirstWide path ∧
      Satisfies x fresh (initial W W) 0 path ∧
      ((tiles x W W fresh (initial W W) 0 path).Perm tl ∨
        (tiles x W W fresh (initial W W) 0 path).Perm (tl.map Rect.transpose)) := by
  obtain ⟨path, fresh, a1, a2, a3, a4⟩ := completeness hW hW h
  cases path with
  | nil => exact ⟨[], fresh, a1, by simp [FirstWide], a2, Or.inl a3⟩
  | cons mv rest =>
    obtain ⟨T, ts, hT, hTx, hTy⟩ := head_tile_origin (x := x) (W := W) (H := W) a1 fresh
    rw [hT] at a3 a4
    obtain ⟨hori, -⟩ := List.forall₂_cons.mp a4
    by_cases hwide : T.w = x * T.h
    · refine ⟨mv :: rest, fresh, a1, ?_, a2, Or.inl (hT ▸ a3)⟩
      simp [FirstWide, hori.mpr hwide]
    · have hTtl : T ∈ tl := a3.mem_iff.mp (by simp)
      have hTtall : T.h = x * T.w := (h.proportion T hTtl).resolve_left hwide
      have h' := h.transpose
      have hmain : (Rect.main W W).transpose = Rect.main W W := rfl
      rw [hmain] at h'
      obtain ⟨path', fresh', b1, b2, b3, b4⟩ := completeness hW hW h'
      rw [List.length_map] at b1
      cases path' with
      | nil => exact ⟨[], fresh', b1, by simp [FirstWide], b2, Or.inr b3⟩
      | cons mv' rest' =>
        obtain ⟨T', ts', hT', hTx', hTy'⟩ := head_tile_origin (x := x) (W := W) (H := W) b1 fresh'
        rw [hT'] at b3 b4
        obtain ⟨hori', -⟩ := List.forall₂_cons.mp b4
        have hT'mem : T' ∈ tl.map Rect.transpose := b3.mem_iff.mp (by simp)
        obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT'mem
        simp only [Rect.transpose] at hTx' hTy' hori'
        have hSnd := h.nondegenerate S hS
        have hTnd := h.nondegenerate T hTtl
        have hST : S = T := by
          apply h.toIsTiling.eq_of_not_disjoint hS hTtl
          apply Rect.not_disjoint_inner_of_overlap
          · rw [hTx, hTy']
            simp only [max_self, zero_add, lt_min_iff]
            exact ⟨hSnd.1, hTnd.1⟩
          · rw [hTy, hTx']
            simp only [max_self, zero_add, lt_min_iff]
            exact ⟨hSnd.2, hTnd.2⟩
        subst hST
        refine ⟨mv' :: rest', fresh', b1, ?_, b2, Or.inr (hT' ▸ b3)⟩
        simp [FirstWide, hori'.mpr hTtall]

end Rectiling
