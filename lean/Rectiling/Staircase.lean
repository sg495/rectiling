-- SPDX-License-Identifier: LGPL-3.0-or-later
import Mathlib

/-!
# The staircase

Model of `src/staircase.rs`: placements, the admissibility rules, the effect of a placement on the tiers, and the constraints that a placement emits.
The model is generic in the representation of lengths, as the Rust code is.
-/

namespace Rectiling

/-- Extent of a tile relative to the tier on which it is placed. -/
inductive Fit
  /-- Narrower than the floor and lower than the wall. -/
  | inside
  /-- Narrower than the floor and as high as the wall. -/
  | fullHeight
  /-- As wide as the floor and lower than the wall. -/
  | fullWidth
  /-- As wide as the floor and as high as the wall. -/
  | full
  deriving DecidableEq, Repr

namespace Fit

/-- Whether the tile is narrower than the floor. -/
def narrow : Fit → Bool
  | inside | fullHeight => true
  | fullWidth | full => false

/-- Whether the tile is lower than the wall. -/
def low : Fit → Bool
  | inside | fullWidth => true
  | fullHeight | full => false

end Fit

/-- Placement of one tile at the anchor of a tier. -/
structure Placement where
  /-- Index of the tier, counted from the top-left. -/
  tier : ℕ
  /-- Extent of the tile relative to the tier. -/
  fit : Fit
  /-- Whether the long side of the tile is vertical. -/
  tall : Bool
  deriving DecidableEq, Repr

/-- Tier of the staircase. -/
structure Tier (L : Type) where
  /-- Length of the floor. -/
  floor : L
  /-- Height of the wall. -/
  wall : L
  /-- Whether no tile can be placed until the floor grows. -/
  stale : Bool
  /-- Whether a tile already stands on the segment carrying the floor. -/
  started : Bool

/-- Arithmetic of lengths. -/
structure Algebra (L : Type) where
  /-- Sum. -/
  add : L → L → L
  /-- Difference. -/
  sub : L → L → L
  /-- Product with the tile proportion. -/
  mulX : L → L
  /-- Quotient by the tile proportion. -/
  divX : L → L

/-- The arithmetic of lengths that carry no information. -/
def unitAlgebra : Algebra Unit :=
  ⟨fun _ _ => (), fun _ _ => (), fun _ => (), fun _ => ()⟩

/-- The arithmetic of real lengths, for a given tile proportion. -/
noncomputable def realAlgebra (x : ℝ) : Algebra ℝ :=
  ⟨(· + ·), (· - ·), (x * ·), (· / x)⟩

/-- Applies a function to the last element of a list. -/
def onLast {α : Type} (f : α → α) : List α → List α
  | [] => []
  | [a] => [f a]
  | a :: b :: l => a :: onLast f (b :: l)

/-- Applies a function to the first element of a list. -/
def onHead {α : Type} (f : α → α) : List α → List α
  | [] => []
  | a :: l => f a :: l

@[simp]
theorem onLast_nil {α : Type} (f : α → α) : onLast f [] = [] :=
  rfl

@[simp]
theorem onLast_concat {α : Type} (f : α → α) (l : List α) (a : α) :
    onLast f (l ++ [a]) = l ++ [f a] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases l with
    | nil => rfl
    | cons c l => simpa [onLast] using ih

@[simp]
theorem length_onLast {α : Type} (f : α → α) (l : List α) : (onLast f l).length = l.length := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩ <;> simp

@[simp]
theorem length_onHead {α : Type} (f : α → α) (l : List α) : (onHead f l).length = l.length := by
  cases l <;> rfl

section Model

variable {L : Type}

/-- Width and height of the tile of a placement, given the floor and the wall of its tier and its free side. -/
def tileSize (A : Algebra L) (fit : Fit) (tall : Bool) (floor wall side : L) : L × L :=
  match fit, tall with
  | .inside, true => (side, A.mulX side)
  | .inside, false => (A.mulX side, side)
  | .fullHeight, false => (A.mulX wall, wall)
  | .fullHeight, true => (A.divX wall, wall)
  | .fullWidth, false => (floor, A.divX floor)
  | .fullWidth, true => (floor, A.mulX floor)
  | .full, _ => (floor, wall)

/-- The length that a placement constrains to be positive. -/
def positiveOf (fit : Fit) (floor wall side : L) : L :=
  match fit with
  | .inside => side
  | .fullHeight => wall
  | .fullWidth | .full => floor

/-- The length that a placement constrains to vanish, if any. -/
def equationOf (A : Algebra L) (fit : Fit) (tall : Bool) (floor wall : L) : Option L :=
  match fit, tall with
  | .full, false => some (A.sub floor (A.mulX wall))
  | .full, true => some (A.sub wall (A.mulX floor))
  | _, _ => none

/-- The tiers before the tier of a placement, after the placement of a tile of the given width. -/
def preAfter (A : Algebra L) (fit : Fit) (width : L) (pre : List (Tier L)) : List (Tier L) :=
  let stale := pre.map fun p => { p with stale := true }
  if fit.low then stale
  else onLast (fun p => { p with stale := false, floor := A.add p.floor width }) stale

/-- The tiers that replace the tier of a placement. -/
def midAfter (A : Algebra L) (fit : Fit) (t : Tier L) (width height : L) : List (Tier L) :=
  match fit with
  | .inside => [⟨width, A.sub t.wall height, false, false⟩, ⟨A.sub t.floor width, height, false, true⟩]
  | .fullHeight => [⟨A.sub t.floor width, t.wall, false, true⟩]
  | .fullWidth => [⟨t.floor, A.sub t.wall height, false, false⟩]
  | .full => []

/-- The tiers after the tier of a placement, after the placement of a tile of the given height. -/
def postAfter (A : Algebra L) (fit : Fit) (height : L) (post : List (Tier L)) : List (Tier L) :=
  if fit.narrow then post else onHead (fun q => { q with wall := A.add q.wall height }) post

/-- The staircase of an empty main rectangle. -/
def initial (width height : L) : List (Tier L) :=
  [⟨width, height, false, false⟩]

/-- The staircase after a placement; `side` is the free side of the tile, used by inside placements only. -/
def place (A : Algebra L) (s : List (Tier L)) (mv : Placement) (side : L) : List (Tier L) :=
  match s[mv.tier]? with
  | none => s
  | some t =>
    let size := tileSize A mv.fit mv.tall t.floor t.wall side
    preAfter A mv.fit size.1 (s.take mv.tier) ++ midAfter A mv.fit t size.1 size.2 ++
      postAfter A mv.fit size.2 (s.drop (mv.tier + 1))

/-- The positivity constraint of a placement. -/
def positiveAt (s : List (Tier L)) (mv : Placement) (side : L) : Option L :=
  s[mv.tier]?.map fun t => positiveOf mv.fit t.floor t.wall side

/-- The equation of a placement, if any. -/
def equationAt (A : Algebra L) (s : List (Tier L)) (mv : Placement) : Option L :=
  s[mv.tier]?.bind fun t => equationOf A mv.fit mv.tall t.floor t.wall

/-- The number of tiers after a placement of the given fit on a staircase with `count` tiers. -/
def tiersAfter (count : ℕ) : Fit → ℕ
  | .inside => count + 1
  | .full => count - 1
  | _ => count

/-- The rules on stale tiers and started floors: the tier exists and is not stale, and a tile as high as the wall is not placed when the floor of the previous tier is started. -/
def Allows (s : List (Tier L)) (mv : Placement) : Prop :=
  (∃ t, s[mv.tier]? = some t ∧ t.stale = false) ∧
    (mv.fit.low = false → 0 < mv.tier → ∀ p, s[mv.tier - 1]? = some p → p.started = false)

/-- Admissibility of a placement with the given number of tiles still to place, as in `Staircase::admits`. -/
def Admits (s : List (Tier L)) (mv : Placement) (remaining : ℕ) : Prop :=
  Allows s mv ∧ 0 < remaining ∧ tiersAfter s.length mv.fit ≤ remaining - 1 ∧
    (tiersAfter s.length mv.fit = 0 → remaining - 1 = 0)

/-- The number of inside placements after a placement, given their number before it. -/
def nextIndex (k : ℕ) (mv : Placement) : ℕ :=
  if mv.fit = .inside then k + 1 else k

/-- The staircase after a sequence of placements; `fresh j` is the free side of the inside placement of index `j`, and `k` the number of inside placements made before the sequence. -/
def finalStairs (A : Algebra L) (fresh : ℕ → L) : List (Tier L) → ℕ → List Placement → List (Tier L)
  | s, _, [] => s
  | s, k, mv :: rest => finalStairs A fresh (place A s mv (fresh k)) (nextIndex k mv) rest

/-- The positivity constraints emitted by a sequence of placements, one per tile. -/
def positives (A : Algebra L) (fresh : ℕ → L) : List (Tier L) → ℕ → List Placement → List L
  | _, _, [] => []
  | s, k, mv :: rest =>
    (positiveAt s mv (fresh k)).toList ++
      positives A fresh (place A s mv (fresh k)) (nextIndex k mv) rest

/-- The equations emitted by a sequence of placements, one per full tile. -/
def equations (A : Algebra L) (fresh : ℕ → L) : List (Tier L) → ℕ → List Placement → List L
  | _, _, [] => []
  | s, k, mv :: rest =>
    (equationAt A s mv).toList ++ equations A fresh (place A s mv (fresh k)) (nextIndex k mv) rest

/-- A sequence of placements each of which obeys the rules on stale tiers and started floors, and which empties the staircase. -/
def Allowed (A : Algebra L) (fresh : ℕ → L) : List (Tier L) → ℕ → List Placement → Prop
  | s, _, [] => s = []
  | s, k, mv :: rest =>
    Allows s mv ∧ Allowed A fresh (place A s mv (fresh k)) (nextIndex k mv) rest

/-- A sequence of placements each of which is admissible, and which empties the staircase. -/
def CompleteFrom (s : List (Tier Unit)) (remaining : ℕ) : List Placement → Prop
  | [] => s = []
  | mv :: rest =>
    Admits s mv remaining ∧ CompleteFrom (place unitAlgebra s mv ()) (remaining - 1) rest

end Model

/-- Complete admissible placement sequence for `n` tiles, as enumerated by the search. -/
def Complete (n : ℕ) (path : List Placement) : Prop :=
  CompleteFrom (initial () ()) n path

/-- The first tile is wide, as the search requires when the main rectangle is a square. -/
def FirstWide (path : List Placement) : Prop :=
  ∀ mv ∈ path.head?, mv.tall = false

/-! ### Decomposition of a placement -/

section Lemmas

variable {L : Type}

theorem place_append (A : Algebra L) (pre post : List (Tier L)) (t : Tier L) (mv : Placement)
    (side : L) (h : mv.tier = pre.length) :
    place A (pre ++ t :: post) mv side =
      preAfter A mv.fit (tileSize A mv.fit mv.tall t.floor t.wall side).1 pre ++
        midAfter A mv.fit t (tileSize A mv.fit mv.tall t.floor t.wall side).1
          (tileSize A mv.fit mv.tall t.floor t.wall side).2 ++
        postAfter A mv.fit (tileSize A mv.fit mv.tall t.floor t.wall side).2 post := by
  simp [place, h]

theorem positiveAt_append (pre post : List (Tier L)) (t : Tier L) (mv : Placement) (side : L)
    (h : mv.tier = pre.length) :
    positiveAt (pre ++ t :: post) mv side = some (positiveOf mv.fit t.floor t.wall side) := by
  simp [positiveAt, h]

theorem equationAt_append (A : Algebra L) (pre post : List (Tier L)) (t : Tier L) (mv : Placement)
    (h : mv.tier = pre.length) :
    equationAt A (pre ++ t :: post) mv = equationOf A mv.fit mv.tall t.floor t.wall := by
  simp [equationAt, h]

/-- A valid tier index splits the staircase around the tier. -/
theorem exists_split {s : List (Tier L)} {i : ℕ} {t : Tier L} (h : s[i]? = some t) :
    ∃ pre post, s = pre ++ t :: post ∧ i = pre.length := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨s.take i, s.drop (i + 1), ?_, ?_⟩
  · simp
  · simp [Nat.le_of_lt hi]

theorem allows_append {pre post : List (Tier L)} {t : Tier L} {mv : Placement}
    (h : mv.tier = pre.length) :
    Allows (pre ++ t :: post) mv ↔
      t.stale = false ∧ (mv.fit.low = false → ∀ p ∈ pre.getLast?, p.started = false) := by
  unfold Allows
  have h1 : (pre ++ t :: post)[mv.tier]? = some t := by simp [h]
  rw [h1]
  constructor
  · rintro ⟨⟨t', ht', hs⟩, hprev⟩
    obtain rfl : t = t' := by simpa using ht'
    refine ⟨hs, fun hlow p hp => ?_⟩
    rcases List.eq_nil_or_concat pre with rfl | ⟨pre', a, rfl⟩
    · simp at hp
    · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, Option.mem_def, Option.some.injEq] at hp
      subst hp
      refine hprev hlow (by simp [h]) a ?_
      simp [h]
  · rintro ⟨hs, hprev⟩
    refine ⟨⟨t, rfl, hs⟩, fun hlow hpos p hp => hprev hlow p ?_⟩
    rcases List.eq_nil_or_concat pre with rfl | ⟨pre', a, rfl⟩
    · simp at h
      omega
    · simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
        zero_add] at h
      simp only [h, List.concat_eq_append, add_tsub_cancel_right, List.append_assoc,
        List.cons_append, List.nil_append] at hp
      rw [List.getElem?_append_right (le_refl _)] at hp
      simp only [tsub_self, List.getElem?_cons_zero, Option.some.injEq] at hp
      simp [hp]

@[simp]
theorem length_preAfter (A : Algebra L) (fit : Fit) (w : L) (pre : List (Tier L)) :
    (preAfter A fit w pre).length = pre.length := by
  unfold preAfter
  split <;> simp

theorem length_midAfter_add (A : Algebra L) (fit : Fit) (t : Tier L) (w h : L) (a b : ℕ) :
    a + (midAfter A fit t w h).length + b = tiersAfter (a + 1 + b) fit := by
  cases fit <;> simp [midAfter, tiersAfter]
  omega

@[simp]
theorem length_postAfter (A : Algebra L) (fit : Fit) (h : L) (post : List (Tier L)) :
    (postAfter A fit h post).length = post.length := by
  unfold postAfter
  split <;> simp

theorem length_place (A : Algebra L) {s : List (Tier L)} {mv : Placement} (side : L) {t : Tier L}
    (h : s[mv.tier]? = some t) : (place A s mv side).length = tiersAfter s.length mv.fit := by
  obtain ⟨pre, post, rfl, hi⟩ := exists_split h
  rw [place_append A pre post t mv side hi]
  simp only [List.length_append, length_preAfter, length_postAfter, List.length_cons]
  rw [show pre.length + (post.length + 1) = pre.length + 1 + post.length by omega]
  exact length_midAfter_add A mv.fit t _ _ _ _

end Lemmas

/-! ### Change of the representation of lengths -/

section Map

variable {L M : Type}

/-- The tier with its lengths mapped by a function. -/
def Tier.map (f : L → M) (t : Tier L) : Tier M :=
  ⟨f t.floor, f t.wall, t.stale, t.started⟩

/-- Compatibility of a function with two arithmetics of lengths. -/
structure Algebra.IsHom (A : Algebra L) (B : Algebra M) (f : L → M) : Prop where
  add : ∀ a b, f (A.add a b) = B.add (f a) (f b)
  sub : ∀ a b, f (A.sub a b) = B.sub (f a) (f b)
  mulX : ∀ a, f (A.mulX a) = B.mulX (f a)
  divX : ∀ a, f (A.divX a) = B.divX (f a)

theorem Algebra.isHom_unit (A : Algebra L) : A.IsHom unitAlgebra fun _ => () :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable {A : Algebra L} {B : Algebra M} {f : L → M}

theorem tileSize_map (hf : A.IsHom B f) (fit : Fit) (tall : Bool) (floor wall side : L) :
    tileSize B fit tall (f floor) (f wall) (f side) =
      ((fun p : L × L => (f p.1, f p.2)) (tileSize A fit tall floor wall side)) := by
  cases fit <;> cases tall <;> simp [tileSize, hf.mulX, hf.divX]

theorem onLast_map {α β : Type} (g : α → β) (u : α → α) (v : β → β) (h : ∀ a, g (u a) = v (g a))
    (l : List α) : (onLast u l).map g = onLast v (l.map g) := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩ <;> simp [h]

theorem onHead_map {α β : Type} (g : α → β) (u : α → α) (v : β → β) (h : ∀ a, g (u a) = v (g a))
    (l : List α) : (onHead u l).map g = onHead v (l.map g) := by
  cases l <;> simp [onHead, h]

theorem preAfter_map (hf : A.IsHom B f) (fit : Fit) (w : L) (pre : List (Tier L)) :
    (preAfter A fit w pre).map (Tier.map f) = preAfter B fit (f w) (pre.map (Tier.map f)) := by
  unfold preAfter
  split
  · simp [Tier.map]
  · rw [onLast_map (Tier.map f) _ (fun p => { p with stale := false, floor := B.add p.floor (f w) })]
    · simp only [List.map_map]
      rfl
    · intro a
      simp [Tier.map, hf.add]

theorem midAfter_map (hf : A.IsHom B f) (fit : Fit) (t : Tier L) (w h : L) :
    (midAfter A fit t w h).map (Tier.map f) = midAfter B fit (Tier.map f t) (f w) (f h) := by
  cases fit <;> simp [midAfter, Tier.map, hf.sub]

theorem postAfter_map (hf : A.IsHom B f) (fit : Fit) (h : L) (post : List (Tier L)) :
    (postAfter A fit h post).map (Tier.map f) = postAfter B fit (f h) (post.map (Tier.map f)) := by
  unfold postAfter
  split
  · rfl
  · rw [onHead_map (Tier.map f)]
    intro a
    simp [Tier.map, hf.add]

theorem place_map (hf : A.IsHom B f) (s : List (Tier L)) (mv : Placement) (side : L) :
    (place A s mv side).map (Tier.map f) = place B (s.map (Tier.map f)) mv (f side) := by
  cases hs : s[mv.tier]? with
  | none => simp [place, hs]
  | some t =>
    obtain ⟨pre, post, rfl, hi⟩ := exists_split hs
    have hi' : mv.tier = (pre.map (Tier.map f)).length := by simpa using hi
    have hm : (pre ++ t :: post).map (Tier.map f) =
        pre.map (Tier.map f) ++ Tier.map f t :: post.map (Tier.map f) := by simp
    rw [place_append A pre post t mv side hi, hm, place_append B _ _ _ mv (f side) hi']
    have hsz := tileSize_map hf mv.fit mv.tall t.floor t.wall side
    change tileSize B mv.fit mv.tall (Tier.map f t).floor (Tier.map f t).wall (f side) = _ at hsz
    rw [hsz, List.map_append, List.map_append, preAfter_map hf, midAfter_map hf, postAfter_map hf]

theorem allows_map (s : List (Tier L)) (mv : Placement) :
    Allows (s.map (Tier.map f)) mv ↔ Allows s mv := by
  unfold Allows
  simp only [List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨t, ⟨t', ht', rfl⟩, hs⟩, hp⟩
    exact ⟨⟨t', ht', hs⟩, fun hl h0 p hpp => hp hl h0 _ ⟨p, hpp, rfl⟩⟩
  · rintro ⟨⟨t, ht, hs⟩, hp⟩
    refine ⟨⟨_, ⟨t, ht, rfl⟩, hs⟩, ?_⟩
    rintro hl h0 _ ⟨p, hpp, rfl⟩
    exact hp hl h0 p hpp

theorem positiveAt_map (s : List (Tier L)) (mv : Placement) (side : L) :
    positiveAt (s.map (Tier.map f)) mv (f side) = (positiveAt s mv side).map f := by
  unfold positiveAt
  cases hs : s[mv.tier]? with
  | none => simp [hs]
  | some t => cases hfit : mv.fit <;> simp [hs, positiveOf, Tier.map]

theorem equationAt_map (hf : A.IsHom B f) (s : List (Tier L)) (mv : Placement) :
    equationAt B (s.map (Tier.map f)) mv = (equationAt A s mv).map f := by
  unfold equationAt
  cases hs : s[mv.tier]? with
  | none => simp [hs]
  | some t =>
    cases hfit : mv.fit <;> cases htall : mv.tall <;>
      simp [hs, equationOf, Tier.map, hf.sub, hf.mulX]

theorem finalStairs_map (hf : A.IsHom B f) (fresh : ℕ → L) (s : List (Tier L)) (k : ℕ)
    (path : List Placement) :
    (finalStairs A fresh s k path).map (Tier.map f) =
      finalStairs B (f ∘ fresh) (s.map (Tier.map f)) k path := by
  induction path generalizing s k with
  | nil => rfl
  | cons mv rest ih => simp [finalStairs, ih, place_map hf]

theorem positives_map (hf : A.IsHom B f) (fresh : ℕ → L) (s : List (Tier L)) (k : ℕ)
    (path : List Placement) :
    positives B (f ∘ fresh) (s.map (Tier.map f)) k path = (positives A fresh s k path).map f := by
  induction path generalizing s k with
  | nil => rfl
  | cons mv rest ih =>
    simp only [positives, Function.comp_apply, List.map_append, positiveAt_map,
      ← place_map hf, ih]
    cases positiveAt s mv (fresh k) <;> rfl

theorem equations_map (hf : A.IsHom B f) (fresh : ℕ → L) (s : List (Tier L)) (k : ℕ)
    (path : List Placement) :
    equations B (f ∘ fresh) (s.map (Tier.map f)) k path = (equations A fresh s k path).map f := by
  induction path generalizing s k with
  | nil => rfl
  | cons mv rest ih =>
    simp only [equations, Function.comp_apply, List.map_append, equationAt_map hf,
      ← place_map hf, ih]
    cases equationAt A s mv <;> rfl

theorem allowed_map (hf : A.IsHom B f) (fresh : ℕ → L) (s : List (Tier L)) (k : ℕ)
    (path : List Placement) :
    Allowed B (f ∘ fresh) (s.map (Tier.map f)) k path ↔ Allowed A fresh s k path := by
  induction path generalizing s k with
  | nil => simp [Allowed]
  | cons mv rest ih =>
    simp only [Allowed, Function.comp_apply, allows_map, ← place_map hf, ih]

end Map

/-! ### Free sides -/

section Sides

variable {L : Type}

theorem tileSize_side (A : Algebra L) {fit : Fit} (tall : Bool) (floor wall a b : L)
    (h : fit ≠ .inside) : tileSize A fit tall floor wall a = tileSize A fit tall floor wall b := by
  cases fit <;> cases tall <;> simp_all [tileSize]

/-- The free side is used by inside placements only. -/
theorem place_side (A : Algebra L) (s : List (Tier L)) (mv : Placement) (a b : L)
    (h : mv.fit ≠ .inside) : place A s mv a = place A s mv b := by
  unfold place
  cases s[mv.tier]? with
  | none => rfl
  | some t => simp only [tileSize_side A mv.tall t.floor t.wall a b h]

theorem positiveAt_side (s : List (Tier L)) (mv : Placement) (a b : L) (h : mv.fit ≠ .inside) :
    positiveAt s mv a = positiveAt s mv b := by
  unfold positiveAt
  cases hfit : mv.fit <;> simp_all [positiveOf]

theorem le_nextIndex (k : ℕ) (mv : Placement) : k ≤ nextIndex k mv := by
  unfold nextIndex
  split <;> omega

/-- The number of inside placements after a sequence of placements, given their number before it. -/
def finalIndex (k : ℕ) : List Placement → ℕ
  | [] => k
  | mv :: rest => finalIndex (nextIndex k mv) rest

theorem le_finalIndex (k : ℕ) (path : List Placement) : k ≤ finalIndex k path := by
  induction path generalizing k with
  | nil => exact le_refl k
  | cons mv rest ih => exact (le_nextIndex k mv).trans (ih _)

/-- A sequence of placements depends only on the free sides of its inside placements. -/
theorem run_congr (A : Algebra L) {f g : ℕ → L} (path : List Placement) :
    ∀ (s : List (Tier L)) (k : ℕ), (∀ j, k ≤ j → j < finalIndex k path → f j = g j) →
      (Allowed A f s k path ↔ Allowed A g s k path) ∧
        positives A f s k path = positives A g s k path ∧
        equations A f s k path = equations A g s k path := by
  induction path with
  | nil => intro s k _; exact ⟨Iff.rfl, rfl, rfl⟩
  | cons mv rest ih =>
    intro s k hfg
    have hside : place A s mv (f k) = place A s mv (g k) ∧
        positiveAt s mv (f k) = positiveAt s mv (g k) := by
      by_cases hfit : mv.fit = .inside
      · have hk : f k = g k := by
          refine hfg k (le_refl k) ?_
          have := le_finalIndex (nextIndex k mv) rest
          simp only [nextIndex, hfit, ite_true] at this
          simp only [finalIndex, nextIndex, hfit, ite_true]
          exact this
        rw [hk]
        exact ⟨rfl, rfl⟩
      · exact ⟨place_side A s mv _ _ hfit, positiveAt_side s mv _ _ hfit⟩
    obtain ⟨i1, i2, i3⟩ := ih (place A s mv (g k)) (nextIndex k mv)
      fun j hj hj' => hfg j ((le_nextIndex k mv).trans hj) hj'
    simp only [Allowed, positives, equations, hside.1, hside.2, i1, i2, i3, and_self]

set_option linter.unusedSimpArgs false in
/-- A sequence that obeys the rules and empties the staircase emits as many equations as it has inside placements and the staircase has tiers. -/
theorem length_equations (A : Algebra L) (fresh : ℕ → L) (path : List Placement) :
    ∀ (s : List (Tier L)) (k : ℕ), Allowed A fresh s k path →
      s.length + finalIndex k path = (equations A fresh s k path).length + k := by
  induction path with
  | nil =>
    intro s k h
    simp only [Allowed] at h
    subst h
    simp [finalIndex, equations]
  | cons mv rest ih =>
    intro s k h
    obtain ⟨hallow, hrest⟩ := h
    obtain ⟨⟨t, ht, -⟩, -⟩ := id hallow
    have hlen := length_place A (fresh k) ht
    have hih := ih _ _ hrest
    obtain ⟨pre, post, rfl, hi⟩ := exists_split ht
    rw [hlen] at hih
    simp only [equations, finalIndex, List.length_append, equationAt_append A pre post t mv hi,
      List.length_cons] at hih ⊢
    cases hfit : mv.fit <;> cases htall : mv.tall <;>
      simp only [hfit, htall, equationOf, tiersAfter, nextIndex, Option.toList_none,
        Option.toList_some, List.length_nil, List.length_cons, List.length_append, ite_true,
        reduceCtorEq, ite_false] at hih ⊢ <;> omega

end Sides

/-! ### Real lengths -/

/-- The constraints emitted by a sequence of placements hold, for the given proportion and free sides. -/
def Satisfies (x : ℝ) (fresh : ℕ → ℝ) (s : List (Tier ℝ)) (k : ℕ) (path : List Placement) : Prop :=
  (∀ c ∈ positives (realAlgebra x) fresh s k path, 0 < c) ∧
    ∀ e ∈ equations (realAlgebra x) fresh s k path, e = 0

theorem Satisfies.head {x : ℝ} {fresh : ℕ → ℝ} {s : List (Tier ℝ)} {k : ℕ} {mv : Placement}
    {rest : List Placement} (h : Satisfies x fresh s k (mv :: rest)) :
    (∀ c ∈ positiveAt s mv (fresh k), 0 < c) ∧
      ∀ e ∈ equationAt (realAlgebra x) s mv, e = 0 := by
  refine ⟨fun c hc => h.1 c ?_, fun e he => h.2 e ?_⟩
  · simp only [positives, List.mem_append, Option.mem_toList]
    exact Or.inl hc
  · simp only [equations, List.mem_append, Option.mem_toList]
    exact Or.inl he

theorem Satisfies.tail {x : ℝ} {fresh : ℕ → ℝ} {s : List (Tier ℝ)} {k : ℕ} {mv : Placement}
    {rest : List Placement} (h : Satisfies x fresh s k (mv :: rest)) :
    Satisfies x fresh (place (realAlgebra x) s mv (fresh k)) (nextIndex k mv) rest := by
  refine ⟨fun c hc => h.1 c ?_, fun e he => h.2 e ?_⟩
  · simp only [positives, List.mem_append]
    exact Or.inr hc
  · simp only [equations, List.mem_append]
    exact Or.inr he

end Rectiling
