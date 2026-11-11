-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Region

/-!
# Soundness of the staircase

A complete admissible placement sequence, together with a proportion and free sides that satisfy the emitted constraints, yields a tiling of the main rectangle by rectangles of that proportion.

The emitted constraints do not state that a tile placed inside its tier is narrower than the floor or lower than the wall.
These inequalities follow from the rules on stale tiers and started floors: a tier whose floor or wall is not positive can never be removed once it is started, or once the tiers before it are stale.
-/

namespace Rectiling

/-- The constraints emitted by a sequence of placements hold. -/
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

/-- The tile of a placement whose constraints hold has positive sides and the given proportion. -/
theorem size_facts {x : ℝ} (hx : 0 < x) (fit : Fit) (tall : Bool) (floor wall side : ℝ)
    (hp : 0 < positiveOf fit floor wall side)
    (he : ∀ e ∈ equationOf (realAlgebra x) fit tall floor wall, e = 0) :
    0 < (tileSize (realAlgebra x) fit tall floor wall side).1 ∧
      0 < (tileSize (realAlgebra x) fit tall floor wall side).2 ∧
      ((tileSize (realAlgebra x) fit tall floor wall side).1 =
          x * (tileSize (realAlgebra x) fit tall floor wall side).2 ∨
        (tileSize (realAlgebra x) fit tall floor wall side).2 =
          x * (tileSize (realAlgebra x) fit tall floor wall side).1) := by
  have hx' : x ≠ 0 := hx.ne'
  cases fit <;> cases tall <;>
    simp only [tileSize, positiveOf, equationOf, realAlgebra, Option.mem_def, Option.some.injEq,
      forall_eq', reduceCtorEq, IsEmpty.forall_iff, implies_true] at hp he ⊢
  · exact ⟨mul_pos hx hp, hp, Or.inl trivial⟩
  · exact ⟨hp, mul_pos hx hp, Or.inr trivial⟩
  · exact ⟨mul_pos hx hp, hp, Or.inl trivial⟩
  · exact ⟨div_pos hp hx, hp, Or.inr (by field_simp)⟩
  · exact ⟨hp, div_pos hp hx, Or.inl (by field_simp)⟩
  · exact ⟨hp, mul_pos hx hp, Or.inr trivial⟩
  · have hw : floor = x * wall := by linarith
    refine ⟨hp, ?_, Or.inl hw⟩
    rw [hw] at hp
    exact (mul_pos_iff_of_pos_left hx).mp hp
  · have hw : wall = x * floor := by linarith
    exact ⟨hp, hw ▸ mul_pos hx hp, Or.inr hw⟩

/-! ### Tiers that can never be removed -/

/-- Some started floor, or the last floor, is not positive. -/
def DoomF (s : List (Tier ℝ)) : Prop :=
  (∃ t ∈ s, t.floor ≤ 0 ∧ t.started = true) ∨ ∃ t ∈ s.getLast?, t.floor ≤ 0

/-- Some wall is not positive, and every tier before it is stale. -/
def DoomW : List (Tier ℝ) → Prop
  | [] => False
  | t :: rest => t.wall ≤ 0 ∨ (t.stale = true ∧ DoomW rest)

theorem doomW_append (l₁ l₂ : List (Tier ℝ)) :
    DoomW (l₁ ++ l₂) ↔ DoomW l₁ ∨ ((∀ t ∈ l₁, t.stale = true) ∧ DoomW l₂) := by
  induction l₁ with
  | nil => simp [DoomW]
  | cons t l ih =>
    simp only [List.cons_append, DoomW, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem doomW_map_stale {l : List (Tier ℝ)} (h : DoomW l) :
    DoomW (l.map fun p => { p with stale := true }) := by
  induction l with
  | nil => exact h
  | cons t l ih =>
    simp only [List.map_cons, DoomW] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨trivial, ih h.2⟩

theorem doomW_onLast {l : List (Tier ℝ)} (f : Tier ℝ → Tier ℝ) (hf : ∀ p, (f p).wall = p.wall)
    (h : DoomW l) : DoomW (onLast f l) := by
  induction l with
  | nil => exact h
  | cons t l ih =>
    cases l with
    | nil =>
      simp only [DoomW, and_false, or_false] at h
      simp only [onLast, DoomW, and_false, or_false, hf]
      exact h
    | cons u l =>
      simp only [onLast]
      rw [DoomW] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, ih h.2⟩

theorem doomW_preAfter {x : ℝ} {fit : Fit} {w : ℝ} {pre : List (Tier ℝ)} (h : DoomW pre) :
    DoomW (preAfter (realAlgebra x) fit w pre) := by
  unfold preAfter
  split
  · exact doomW_map_stale h
  · exact doomW_onLast _ (fun _ => rfl) (doomW_map_stale h)

theorem preAfter_of_low {L : Type} (A : Algebra L) {fit : Fit} (w : L) (pre : List (Tier L))
    (h : fit.low = true) : preAfter A fit w pre = pre.map fun p => { p with stale := true } := by
  simp [preAfter, h]

theorem preAfter_concat {L : Type} (A : Algebra L) {fit : Fit} (w : L) (pre : List (Tier L))
    (p : Tier L) (h : fit.low = false) :
    preAfter A fit w (pre ++ [p]) =
      (pre.map fun p => { p with stale := true }) ++
        [{ p with stale := false, floor := A.add p.floor w }] := by
  simp [preAfter, h]

theorem mem_postAfter {L : Type} (A : Algebra L) (fit : Fit) (h : L) {post : List (Tier L)}
    {u : Tier L} (hu : u ∈ post) :
    ∃ u' ∈ postAfter A fit h post, u'.floor = u.floor ∧ u'.started = u.started := by
  unfold postAfter
  split
  · exact ⟨u, hu, rfl, rfl⟩
  · cases post with
    | nil => simp at hu
    | cons q rest =>
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact ⟨{ u with wall := A.add u.wall h }, by simp [onHead], rfl, rfl⟩
      · exact ⟨u, by simp [onHead, hu], rfl, rfl⟩

theorem getLast?_postAfter {L : Type} (A : Algebra L) (fit : Fit) (h : L) {post : List (Tier L)}
    {u : Tier L} (hu : u ∈ post.getLast?) :
    ∃ u' ∈ (postAfter A fit h post).getLast?, u'.floor = u.floor := by
  unfold postAfter
  split
  · exact ⟨u, hu, rfl⟩
  · cases post with
    | nil => simp at hu
    | cons q rest =>
      cases rest with
      | nil =>
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hu
        subst hu
        exact ⟨{ q with wall := A.add q.wall h }, by simp [onHead], rfl⟩
      | cons r rest =>
        refine ⟨u, ?_, rfl⟩
        simpa [onHead, List.getLast?_cons_cons] using hu

/-- The hypotheses under which one placement is studied: the staircase is split around the tier, the placement obeys the rules, and its constraints hold. -/
structure StepData (x : ℝ) (pre : List (Tier ℝ)) (t : Tier ℝ) (post : List (Tier ℝ))
    (mv : Placement) (side : ℝ) : Prop where
  x_pos : 0 < x
  tier : mv.tier = pre.length
  fresh : t.stale = false
  prev : mv.fit.low = false → ∀ p ∈ pre.getLast?, p.started = false
  positive : 0 < positiveOf mv.fit t.floor t.wall side
  equation : ∀ e ∈ equationOf (realAlgebra x) mv.fit mv.tall t.floor t.wall, e = 0

/-- The hypotheses on one placement, from the rules and the constraints. -/
theorem exists_stepData {x : ℝ} (hx : 0 < x) {s : List (Tier ℝ)} {mv : Placement} {side : ℝ}
    (ha : Allows s mv) (hp : ∀ c ∈ positiveAt s mv side, 0 < c)
    (he : ∀ e ∈ equationAt (realAlgebra x) s mv, e = 0) :
    ∃ pre t post, s = pre ++ t :: post ∧ StepData x pre t post mv side := by
  obtain ⟨⟨t, ht, -⟩, -⟩ := id ha
  obtain ⟨pre, post, rfl, hi⟩ := exists_split ht
  rw [allows_append hi] at ha
  refine ⟨pre, t, post, rfl, hx, hi, ha.1, ha.2, ?_, ?_⟩
  · exact hp _ (by rw [positiveAt_append _ _ _ _ _ hi]; rfl)
  · rw [equationAt_append _ _ _ _ _ hi] at he
    exact he

section StepLemmas

variable {x : ℝ} {pre post : List (Tier ℝ)} {t : Tier ℝ} {mv : Placement} {side : ℝ}

theorem StepData.size (d : StepData x pre t post mv side) :
    0 < (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 ∧
      0 < (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 ∧
      ((tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 =
          x * (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 ∨
        (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 =
          x * (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1) :=
  size_facts d.x_pos mv.fit mv.tall t.floor t.wall side d.positive d.equation

/-- A wall that is not positive, behind stale tiers, persists. -/
theorem StepData.doomW (d : StepData x pre t post mv side) (h : DoomW (pre ++ t :: post)) :
    DoomW (place (realAlgebra x) (pre ++ t :: post) mv side) := by
  rw [place_append _ pre post t mv side d.tier]
  obtain ⟨hw, hh, -⟩ := d.size
  have hsnd := tileSize_snd_of_not_low (realAlgebra x) mv.tall t.floor t.wall side (fit := mv.fit)
  have hpos := d.positive
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 = w at *
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 = h' at *
  rw [doomW_append] at h
  rw [List.append_assoc, doomW_append]
  rcases h with h | ⟨hstale, h⟩
  · exact Or.inl (doomW_preAfter h)
  · rw [DoomW] at h
    rcases h with h | h
    · cases hfit : mv.fit
      · refine Or.inr ⟨?_, ?_⟩
        · rw [preAfter_of_low _ _ _ (by simp [Fit.low])]
          simp
        · simp only [midAfter, List.cons_append, DoomW, realAlgebra]
          exact Or.inl (by linarith)
      · have := hsnd (by simp [hfit, Fit.low])
        linarith
      · refine Or.inr ⟨?_, ?_⟩
        · rw [preAfter_of_low _ _ _ (by simp [Fit.low])]
          simp
        · simp only [midAfter, List.cons_append, DoomW, realAlgebra]
          exact Or.inl (by linarith)
      · have := hsnd (by simp [hfit, Fit.low])
        linarith
    · rw [d.fresh] at h
      exact absurd h.1 (by simp)

/-- A floor that is not positive, and is started or last, persists. -/
theorem StepData.doomF (d : StepData x pre t post mv side) (h : DoomF (pre ++ t :: post)) :
    DoomF (place (realAlgebra x) (pre ++ t :: post) mv side) := by
  rw [place_append _ pre post t mv side d.tier]
  obtain ⟨hw, hh, -⟩ := d.size
  have hfst := tileSize_fst_of_not_narrow (realAlgebra x) mv.tall t.floor t.wall side (fit := mv.fit)
  have hpos := d.positive
  have hprev := d.prev
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 = w at *
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 = h' at *
  -- the tier of the placement
  have hmid : t.floor ≤ 0 → (t.started = true ∨ post = []) →
      DoomF (preAfter (realAlgebra x) mv.fit w pre ++ midAfter (realAlgebra x) mv.fit t w h' ++
        postAfter (realAlgebra x) mv.fit h' post) := by
    intro hf _
    cases hfit : mv.fit
    · refine Or.inl ⟨⟨t.floor - w, h', false, true⟩, ?_, ?_, rfl⟩
      · simp [midAfter, realAlgebra]
      · simp only
        linarith
    · refine Or.inl ⟨⟨t.floor - w, t.wall, false, true⟩, ?_, ?_, rfl⟩
      · simp [midAfter, realAlgebra]
      · simp only
        linarith
    · rw [hfit] at hpos
      simp only [positiveOf] at hpos
      linarith
    · rw [hfit] at hpos
      simp only [positiveOf] at hpos
      linarith
  rcases h with ⟨u, hu, hf, hst⟩ | ⟨u, hu, hf⟩
  · simp only [List.mem_append, List.mem_cons] at hu
    rcases hu with hu | rfl | hu
    · refine Or.inl ?_
      cases hlow : mv.fit.low
      · rcases List.eq_nil_or_concat pre with rfl | ⟨pre', a, rfl⟩
        · simp at hu
        · simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hu
          rcases hu with hu | rfl
          · refine ⟨{ u with stale := true }, ?_, hf, hst⟩
            rw [List.concat_eq_append, preAfter_concat _ _ _ _ hlow]
            simp only [List.mem_append, List.mem_map]
            exact Or.inl (Or.inl (Or.inl ⟨u, hu, rfl⟩))
          · have := hprev hlow u (by simp)
            rw [this] at hst
            exact absurd hst (by simp)
      · refine ⟨{ u with stale := true }, ?_, hf, hst⟩
        rw [preAfter_of_low _ _ _ hlow]
        simp only [List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨u, hu, rfl⟩)
    · exact hmid hf (Or.inl hst)
    · obtain ⟨u', hu', h1, h2⟩ := mem_postAfter (realAlgebra x) mv.fit h' hu
      exact Or.inl ⟨u', by simp [hu'], by rw [h1]; exact hf, by rw [h2]; exact hst⟩
  · cases post with
    | nil =>
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
        Option.some.injEq] at hu
      subst hu
      exact hmid hf (Or.inr rfl)
    | cons q rest =>
      have hu' : u ∈ (q :: rest).getLast? := by
        simpa [List.getLast?_append, List.getLast?_cons_cons] using hu
      obtain ⟨u', hu'', h1⟩ := getLast?_postAfter (realAlgebra x) mv.fit h' hu'
      refine Or.inr ⟨u', ?_, by rw [h1]; exact hf⟩
      rw [List.getLast?_append]
      rw [Option.mem_def] at hu'' ⊢
      rw [hu'']
      rfl

theorem positive_preAfter {fit : Fit} {w : ℝ} (hw : 0 < w) (h : Positive pre) :
    Positive (preAfter (realAlgebra x) fit w pre) := by
  cases hlow : fit.low
  · rcases List.eq_nil_or_concat pre with rfl | ⟨pre', a, rfl⟩
    · simp [preAfter, Positive]
    · rw [List.concat_eq_append, preAfter_concat _ _ _ _ hlow]
      intro u hu
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hu
      rcases hu with ⟨v, hv, rfl⟩ | rfl
      · exact h v (by simp [hv])
      · have := h a (by simp)
        simp only [realAlgebra]
        exact ⟨by linarith, this.2⟩
  · rw [preAfter_of_low _ _ _ hlow]
    intro u hu
    simp only [List.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact h v hv

theorem positive_postAfter {fit : Fit} {h' : ℝ} (hh : 0 < h') (h : Positive post) :
    Positive (postAfter (realAlgebra x) fit h' post) := by
  unfold postAfter
  split
  · exact h
  · cases post with
    | nil => exact h
    | cons q rest =>
      intro u hu
      simp only [onHead, List.mem_cons] at hu
      rcases hu with rfl | hu
      · have := h q (by simp)
        simp only [realAlgebra]
        exact ⟨this.1, by linarith⟩
      · exact h u (by simp [hu])

/-- Floors and walls stay positive when a tile of positive size is placed that fits its tier strictly where its fit says so. -/
theorem positive_parts {fit : Fit} {w h' : ℝ} (hs : Positive (pre ++ t :: post)) (hw : 0 < w)
    (hh : 0 < h') (hn : fit.narrow = true → w < t.floor) (hl : fit.low = true → h' < t.wall) :
    Positive (preAfter (realAlgebra x) fit w pre ++ midAfter (realAlgebra x) fit t w h' ++
      postAfter (realAlgebra x) fit h' post) := by
  have hpre : Positive pre := fun u hu => hs u (by simp [hu])
  have hpost : Positive post := fun u hu => hs u (by simp [hu])
  have ht := hs t (by simp)
  intro u hu
  simp only [List.mem_append] at hu
  rcases hu with (hu | hu) | hu
  · exact positive_preAfter hw hpre u hu
  · cases fit <;>
      simp only [midAfter, realAlgebra, List.mem_cons, List.not_mem_nil, or_false, Fit.narrow,
        Fit.low, forall_const] at hu hn hl
    · rcases hu with rfl | rfl
      · exact ⟨hw, by linarith⟩
      · exact ⟨by linarith, hh⟩
    · subst hu
      exact ⟨by linarith, ht.2⟩
    · subst hu
      exact ⟨ht.1, by linarith⟩
  · exact positive_postAfter hh hpost u hu

/-- If no floor or wall is doomed after the placement, the tile fits its tier strictly where its fit says so, and floors and walls stay positive. -/
theorem StepData.positive_place (d : StepData x pre t post mv side)
    (hs : Positive (pre ++ t :: post))
    (hF : ¬DoomF (place (realAlgebra x) (pre ++ t :: post) mv side))
    (hW : ¬DoomW (place (realAlgebra x) (pre ++ t :: post) mv side)) :
    (mv.fit.narrow = true → (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 < t.floor) ∧
      (mv.fit.low = true → (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 < t.wall) ∧
      Positive (place (realAlgebra x) (pre ++ t :: post) mv side) := by
  rw [place_append _ pre post t mv side d.tier] at hF hW ⊢
  obtain ⟨hw, hh, -⟩ := d.size
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).1 = w at *
  generalize (tileSize (realAlgebra x) mv.fit mv.tall t.floor t.wall side).2 = h' at *
  have hpre : Positive pre := fun u hu => hs u (by simp [hu])
  have hpost : Positive post := fun u hu => hs u (by simp [hu])
  have ht := hs t (by simp)
  have hn : mv.fit.narrow = true → w < t.floor := by
    intro hnar
    by_contra hc
    apply hF
    cases hfit : mv.fit
    · refine Or.inl ⟨⟨t.floor - w, h', false, true⟩, ?_, ?_, rfl⟩
      · simp [midAfter, realAlgebra]
      · simp only
        linarith
    · refine Or.inl ⟨⟨t.floor - w, t.wall, false, true⟩, ?_, ?_, rfl⟩
      · simp [midAfter, realAlgebra]
      · simp only
        linarith
    · simp [hfit, Fit.narrow] at hnar
    · simp [hfit, Fit.narrow] at hnar
  have hl : mv.fit.low = true → h' < t.wall := by
    intro hlow
    by_contra hc
    apply hW
    rw [List.append_assoc, doomW_append]
    refine Or.inr ⟨?_, ?_⟩
    · rw [preAfter_of_low _ _ _ hlow]
      simp
    · cases hfit : mv.fit
      · simp only [midAfter, List.cons_append, DoomW, realAlgebra]
        exact Or.inl (by linarith)
      · simp [hfit, Fit.low] at hlow
      · simp only [midAfter, List.cons_append, DoomW, realAlgebra]
        exact Or.inl (by linarith)
      · simp [hfit, Fit.low] at hlow
  exact ⟨hn, hl, positive_parts hs hw hh hn hl⟩

end StepLemmas

/-- A staircase with a doomed floor or wall cannot be emptied by placements that obey the rules and whose constraints hold. -/
theorem not_doom {x : ℝ} (hx : 0 < x) (fresh : ℕ → ℝ) (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), Allowed (realAlgebra x) fresh s k path →
      Satisfies x fresh s k path → ¬DoomF s ∧ ¬DoomW s := by
  induction path with
  | nil =>
    intro s k ha _
    simp only [Allowed] at ha
    subst ha
    simp [DoomF, DoomW]
  | cons mv rest ih =>
    intro s k ha hsat
    obtain ⟨hallow, hrest⟩ := ha
    obtain ⟨hp, he⟩ := hsat.head
    obtain ⟨pre, t, post, rfl, d⟩ := exists_stepData hx hallow hp he
    obtain ⟨h1, h2⟩ := ih _ _ hrest hsat.tail
    exact ⟨fun h => h1 (d.doomF h), fun h => h2 (d.doomW h)⟩

/-- The tiles of a sequence of placements that obeys the rules, empties a staircase with positive floors and walls, and whose constraints hold: they have positive sides and the given proportion, lie in the region to be filled, have disjoint interiors and cover the region. -/
theorem tiles_from {x : ℝ} (hx : 0 < x) (W H : ℝ) (fresh : ℕ → ℝ) (path : List Placement) :
    ∀ (s : List (Tier ℝ)) (k : ℕ), Positive s → Allowed (realAlgebra x) fresh s k path →
      Satisfies x fresh s k path →
      (∀ T ∈ tiles x W H fresh s k path,
        T.Nondegenerate ∧ T.HasProportion x ∧ T.closed ⊆ region W H s) ∧
      (tiles x W H fresh s k path).Pairwise (fun S T => Disjoint S.inner T.inner) ∧
      region W H s ⊆ ⋃ T ∈ tiles x W H fresh s k path, T.closed ∧
      (tiles x W H fresh s k path).length = path.length := by
  induction path with
  | nil =>
    intro s k _ ha _
    simp only [Allowed] at ha
    subst ha
    simp [tiles, region_nil]
  | cons mv rest ih =>
    intro s k hs ha hsat
    obtain ⟨hallow, hrest⟩ := ha
    obtain ⟨hp, he⟩ := hsat.head
    obtain ⟨pre, t, post, rfl, d⟩ := exists_stepData hx hallow hp he
    obtain ⟨hF, hW⟩ := not_doom hx fresh rest _ _ hrest hsat.tail
    obtain ⟨hn, hl, hs'⟩ := d.positive_place hs hF hW
    obtain ⟨hw, hh, hprop⟩ := d.size
    obtain ⟨T, hT, ha, hb, hc, hd⟩ := step_region (W := W) (H := H) d.tier hs hw hh hn hl
    obtain ⟨i1, i2, i3, i4⟩ := ih _ _ hs' hrest hsat.tail
    have hTeq := (tileAt_append x W H pre post t mv (fresh k) d.tier).symm.trans hT
    simp only [Option.some.injEq] at hTeq
    simp only [tiles, hT, Option.toList_some, List.singleton_append, List.mem_cons,
      forall_eq_or_imp, List.pairwise_cons, List.length_cons]
    refine ⟨⟨⟨?_, ?_, ha⟩, ?_⟩, ⟨?_, i2⟩, ?_, by rw [i4]⟩
    · rw [← hTeq]
      exact ⟨hw, hh⟩
    · rw [← hTeq]
      exact hprop
    · intro T' hT'
      obtain ⟨j1, j2, j3⟩ := i1 T' hT'
      exact ⟨j1, j2, j3.trans hb⟩
    · intro T' hT'
      exact hd.mono_right ((Rect.inner_subset_closed T').trans (i1 T' hT').2.2)
    · intro p hp
      rcases hc hp with h | h
      · simp only [Set.mem_iUnion, exists_prop]
        exact ⟨T, Or.inl rfl, h⟩
      · have := i3 h
        simp only [Set.mem_iUnion, exists_prop] at this ⊢
        obtain ⟨T', hT', hpT'⟩ := this
        exact ⟨T', Or.inr hT', hpT'⟩

/-! ### Complete admissible sequences -/

theorem CompleteFrom.allowed {s : List (Tier Unit)} {n : ℕ} {path : List Placement} (k : ℕ)
    (h : CompleteFrom s n path) : Allowed unitAlgebra (fun _ => ()) s k path := by
  induction path generalizing s n k with
  | nil => exact h
  | cons mv rest ih => exact ⟨h.1.1, ih _ h.2⟩

theorem CompleteFrom.length {s : List (Tier Unit)} {n : ℕ} {path : List Placement}
    (h : CompleteFrom s n path) (hs : s ≠ []) : path.length = n := by
  induction path generalizing s n with
  | nil => exact absurd h hs
  | cons mv rest ih =>
    obtain ⟨⟨⟨⟨t, ht, -⟩, -⟩, hpos, hle, hzero⟩, hrest⟩ := h
    have hlen := length_place unitAlgebra () ht
    by_cases hs' : place unitAlgebra s mv () = []
    · rw [hs'] at hrest hlen
      have h0 := hzero hlen.symm
      cases rest with
      | nil =>
        simp only [List.length_cons, List.length_nil]
        omega
      | cons mv' rest' =>
        obtain ⟨⟨⟨⟨t', ht', -⟩, -⟩, -⟩, -⟩ := hrest
        simp at ht'
    · have := ih hrest hs'
      simp only [List.length_cons, this]
      omega

theorem Complete.length {n : ℕ} {path : List Placement} (h : Complete n path) : path.length = n :=
  CompleteFrom.length h (by simp [initial])

/-- A complete admissible sequence obeys the rules on stale tiers and started floors, whatever the lengths. -/
theorem Complete.allowed {n : ℕ} {path : List Placement} (h : Complete n path) (x W H : ℝ)
    (fresh : ℕ → ℝ) : Allowed (realAlgebra x) fresh (initial W H) 0 path := by
  have := (allowed_map (Algebra.isHom_unit (realAlgebra x)) fresh (initial W H) 0 path).mp
  exact this (CompleteFrom.allowed 0 h)

/-- **Soundness.** For a complete admissible placement sequence for `n` tiles, a proportion `x ≥ 1` and free sides that satisfy the emitted equations and positivity constraints, the tiles of the sequence form a tiling of the `W × H` rectangle by `n` rectangles of proportion `x`. -/
theorem soundness {x W H : ℝ} {n : ℕ} {path : List Placement} (fresh : ℕ → ℝ) (hx : 1 ≤ x)
    (hpath : Complete n path) (hsat : Satisfies x fresh (initial W H) 0 path) :
    IsSimilarTiling x (Rect.main W H) (tiles x W H fresh (initial W H) 0 path) ∧
      (tiles x W H fresh (initial W H) 0 path).length = n := by
  have hx0 : 0 < x := by linarith
  have hallowed := hpath.allowed x W H fresh
  obtain ⟨hF, hW⟩ := not_doom hx0 fresh path _ _ hallowed hsat
  have hpos : Positive (initial W H) := by
    intro t ht
    simp only [initial, List.mem_singleton] at ht
    subst ht
    constructor
    · by_contra hc
      exact hF (Or.inr ⟨_, by simp [initial], not_lt.mp hc⟩)
    · by_contra hc
      exact hW (Or.inl (not_lt.mp hc))
  obtain ⟨h1, h2, h3, h4⟩ := tiles_from hx0 W H fresh path _ _ hpos hallowed hsat
  rw [region_initial] at h1 h3
  refine ⟨⟨⟨fun T hT => (h1 T hT).1, ?_, h2⟩, hx, fun T hT => (h1 T hT).2.1⟩, h4.trans hpath.length⟩
  apply Set.Subset.antisymm
  · intro p hp
    simp only [Set.mem_iUnion, exists_prop] at hp
    obtain ⟨T, hT, hpT⟩ := hp
    exact (h1 T hT).2.2 hpT
  · exact h3

end Rectiling
