-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Staircase

/-!
# Check of the model against the library

Counts the complete admissible placement sequences of the model, disregarding orientations, as `count_layouts` does in `src/staircase.rs`, and compares the counts with the Baxter numbers that the library reports.
-/

namespace Rectiling

instance {L : Type} (s : List (Tier L)) (mv : Placement) : Decidable (Allows s mv) := by
  unfold Allows
  have d1 : Decidable (∃ t, s[mv.tier]? = some t ∧ t.stale = false) :=
    match h : s[mv.tier]? with
    | none => isFalse (by simp)
    | some t =>
      if hs : t.stale = false then isTrue ⟨t, rfl, hs⟩
      else isFalse (by
        rintro ⟨t', ht', hs'⟩
        cases ht'
        exact hs hs')
  have d2 : Decidable (mv.fit.low = false → 0 < mv.tier →
      ∀ p, s[mv.tier - 1]? = some p → p.started = false) :=
    if hl : mv.fit.low = false then
      if h0 : 0 < mv.tier then
        match h : s[mv.tier - 1]? with
        | none => isTrue (by simp)
        | some q =>
          if hq : q.started = false then isTrue (by
            intro _ _ p hp
            cases hp
            exact hq)
          else isFalse fun hall => hq (hall hl h0 q rfl)
      else isTrue fun _ h => absurd h h0
    else isTrue fun h => absurd h hl
  exact instDecidableAnd

instance {L : Type} (s : List (Tier L)) (mv : Placement) (remaining : ℕ) :
    Decidable (Admits s mv remaining) := by
  unfold Admits
  infer_instance

/-- The number of complete admissible placement sequences from a staircase, disregarding orientations, with a bound on the recursion depth. -/
def countFrom : ℕ → List (Tier Unit) → ℕ → ℕ
  | 0, _, _ => 0
  | depth + 1, s, remaining =>
    if s.isEmpty then 1
    else
      ((List.range s.length).map fun tier =>
        ([Fit.inside, Fit.fullHeight, Fit.fullWidth, Fit.full].map fun fit =>
          if Admits s ⟨tier, fit, false⟩ remaining then
            countFrom depth (place unitAlgebra s ⟨tier, fit, false⟩ ()) (remaining - 1)
          else 0).sum).sum

/-- The number of complete admissible placement sequences for the given number of tiles, disregarding orientations. -/
def countLayouts (tiles : ℕ) : ℕ :=
  countFrom (tiles + 1) (initial () ()) tiles

#guard [1, 2, 3, 4, 5, 6, 7].map countLayouts = [1, 2, 6, 22, 92, 422, 2074]

end Rectiling
