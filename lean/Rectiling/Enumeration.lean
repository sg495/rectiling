-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Check

/-!
# Enumeration of the placement sequences

Model of the enumerations of `src/search.rs` and `src/fast.rs`: the placements tried at a staircase, the complete sequences below a staircase (`Search::sequences` at full depth, `Engine::delegate_rec`, and the sequences visited by `Engine::explore`), and the splitting of the search by prefixes of bounded length (`Search::sequences` and the forced placements of `Engine::explore`).
The sequences enumerated are exactly the complete admissible ones, with the first tile wide when the main rectangle is a square.
-/

namespace Rectiling

/-- The four fits, in the order in which the search tries them. -/
def fits : List Fit :=
  [.inside, .fullHeight, .fullWidth, .full]

/-- The placements at the tiers of a staircase, in the order in which the search tries them. -/
def candidates (count : ℕ) : List Placement :=
  (List.range count).flatMap fun tier =>
    fits.flatMap fun fit => [false, true].map fun tall => ⟨tier, fit, tall⟩

theorem mem_candidates (count : ℕ) (mv : Placement) : mv ∈ candidates count ↔ mv.tier < count := by
  obtain ⟨tier, fit, tall⟩ := mv
  cases fit <;> cases tall <;> simp [candidates, fits]

/-- The placements that the search makes at a staircase: the admissible ones, without the tall ones for the first tile of a square. -/
def moves (square : Bool) (s : List (Tier Unit)) (remaining : ℕ) (first : Bool) : List Placement :=
  (candidates s.length).filter fun mv =>
    decide (Admits s mv remaining) && !(mv.tall && first && square)

theorem mem_moves (square : Bool) (s : List (Tier Unit)) (remaining : ℕ) (first : Bool)
    (mv : Placement) :
    mv ∈ moves square s remaining first ↔
      Admits s mv remaining ∧ (first = true → square = true → mv.tall = false) := by
  simp only [moves, List.mem_filter, mem_candidates, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']
  constructor
  · rintro ⟨-, hadm, hrule⟩
    refine ⟨hadm, fun hf hs => ?_⟩
    cases htall : mv.tall
    · rfl
    · simp [htall, hf, hs] at hrule
  · rintro ⟨hadm, hrule⟩
    refine ⟨?_, hadm, ?_⟩
    · obtain ⟨⟨t, ht, -⟩, -⟩ := hadm.1
      exact (List.getElem?_eq_some_iff.mp ht).1
    · cases hf : first <;> cases hs : square <;> simp_all

/-- The complete sequences below a staircase, with the given number of tiles still to place. -/
def completions (square : Bool) : ℕ → Bool → List (Tier Unit) → List (List Placement)
  | 0, _, s => if s.isEmpty then [[]] else []
  | r + 1, first, s =>
    if s.isEmpty then [[]]
    else
      (moves square s (r + 1) first).flatMap fun mv =>
        (completions square r false (place unitAlgebra s mv ())).map fun p => mv :: p

theorem not_completeFrom_cons_nil (r : ℕ) (mv : Placement) (rest : List Placement) :
    ¬ CompleteFrom ([] : List (Tier Unit)) r (mv :: rest) := by
  rintro ⟨⟨⟨⟨t, ht, -⟩, -⟩, -⟩, -⟩
  simp at ht

/-- **The enumeration lists the complete admissible sequences.** A sequence is enumerated below a staircase exactly when each of its placements is admissible and it empties the staircase, with the first tile wide where the rule for the square applies. -/
theorem mem_completions (square : Bool) :
    ∀ (r : ℕ) (first : Bool) (s : List (Tier Unit)) (p : List Placement),
      p ∈ completions square r first s ↔
        CompleteFrom s r p ∧ (first = true → square = true → FirstWide p) := by
  intro r
  induction r with
  | zero =>
    intro first s p
    rw [completions]
    cases s with
    | nil =>
      cases p with
      | nil => simp [CompleteFrom, FirstWide]
      | cons mv rest => simpa using fun h => absurd h (not_completeFrom_cons_nil 0 mv rest)
    | cons t s =>
      cases p with
      | nil => simp [CompleteFrom]
      | cons mv rest =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, false_iff,
          not_and]
        rintro ⟨⟨-, h0, -⟩, -⟩
        exact absurd h0 (lt_irrefl 0)
  | succ r ih =>
    intro first s p
    rw [completions]
    cases s with
    | nil =>
      cases p with
      | nil => simp [CompleteFrom, FirstWide]
      | cons mv rest => simpa using fun h => absurd h (not_completeFrom_cons_nil (r + 1) mv rest)
    | cons t s =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_map,
        mem_moves]
      cases p with
      | nil =>
        simp [CompleteFrom]
      | cons mv rest =>
        constructor
        · rintro ⟨mv', ⟨hadm, hrule⟩, q, hq, heq⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          refine ⟨⟨hadm, ((ih false _ q).mp hq).1⟩, fun hf hs mv hmv => ?_⟩
          obtain rfl : mv' = mv := by simpa using hmv
          exact hrule hf hs
        · rintro ⟨⟨hadm, hrest⟩, hrule⟩
          exact ⟨mv, ⟨hadm, fun hf hs => hrule hf hs mv (by simp)⟩, rest,
            (ih false _ rest).mpr ⟨hrest, by simp⟩, rfl⟩

/-- The sequences enumerated for `n` tiles are the complete admissible ones, with the first tile wide for a square. -/
theorem mem_completions_initial (square : Bool) (n : ℕ) (p : List Placement) :
    p ∈ completions square n true (initial () ()) ↔
      Complete n p ∧ (square = true → FirstWide p) := by
  rw [mem_completions]
  simp [Complete]

/-! ### Splitting by prefixes -/

/-- The staircase after a sequence of placements. -/
def after (s : List (Tier Unit)) (path : List Placement) : List (Tier Unit) :=
  path.foldl (fun s mv => place unitAlgebra s mv ()) s

/-- The sequences of at most the given length from a staircase, cut where the staircase is emptied, as in `Search::sequences`. -/
def prefixes (square : Bool) : ℕ → ℕ → Bool → List (Tier Unit) → List (List Placement)
  | 0, _, _, _ => [[]]
  | d + 1, r, first, s =>
    if s.isEmpty then [[]]
    else
      (moves square s r first).flatMap fun mv =>
        (prefixes square d (r - 1) false (place unitAlgebra s mv ())).map fun p => mv :: p

/-- **The prefixes split the enumeration.** A sequence is enumerated below a staircase exactly when it consists of one of the prefixes followed by a sequence enumerated below the staircase reached by the prefix. -/
theorem mem_completions_iff_prefix (square : Bool) :
    ∀ (d r : ℕ) (first : Bool) (s : List (Tier Unit)) (p : List Placement),
      p ∈ completions square r first s ↔
        ∃ pre ∈ prefixes square d r first s, ∃ q, p = pre ++ q ∧
          q ∈ completions square (r - pre.length) (first && pre.isEmpty) (after s pre) := by
  intro d
  induction d with
  | zero =>
    intro r first s p
    simp [prefixes, after]
  | succ d ih =>
    intro r first s p
    rw [prefixes]
    cases s with
    | nil => simp [after]
    | cons t s =>
      cases r with
      | zero =>
        have hmoves : moves square (t :: s) 0 first = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro mv hmv
          exact absurd ((mem_moves _ _ _ _ _).mp hmv).1.2.1 (lt_irrefl 0)
        simp [completions, hmoves]
      | succ r =>
        rw [completions]
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap,
          List.mem_map, Nat.add_sub_cancel]
        constructor
        · rintro ⟨mv, hmv, p', hp', rfl⟩
          obtain ⟨pre, hpre, q, rfl, hq⟩ := (ih r false _ p').mp hp'
          refine ⟨mv :: pre, ⟨mv, hmv, pre, hpre, rfl⟩, q, rfl, ?_⟩
          simpa [after] using hq
        · rintro ⟨_, ⟨mv, hmv, pre, hpre, rfl⟩, q, rfl, hq⟩
          refine ⟨mv, hmv, pre ++ q, (ih r false _ _).mpr ⟨pre, hpre, q, rfl, ?_⟩, rfl⟩
          simpa [after] using hq

end Rectiling
