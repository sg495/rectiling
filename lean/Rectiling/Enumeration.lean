-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Check

/-!
# Enumeration of the placement sequences

Model of the enumerations of `src/search.rs` and `src/fast.rs`: the placements tried at a staircase, the complete sequences below a staircase (`Search::sequences` at full depth, `Engine::delegate_rec` beyond the forced placements, and the sequences visited by `Engine::explore`), the splitting of the search by prefixes of bounded length (`Search::sequences` and the forced placements of `Engine::explore`), and the complete sequences that follow forced placements (`Engine::delegate_rec`).
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

theorem cons_mem_completions_iff (square : Bool) (r : ℕ) (first : Bool) (s : List (Tier Unit))
    (mv : Placement) (q : List Placement) :
    (mv :: q) ∈ completions square r first s ↔
      mv ∈ moves square s r first ∧
        q ∈ completions square (r - 1) false (place unitAlgebra s mv ()) := by
  rw [mem_completions, mem_moves, mem_completions]
  simp only [CompleteFrom, FirstWide, List.head?_cons, Option.mem_def, Option.some.injEq,
    forall_eq', Bool.false_eq_true, false_implies, and_true]
  tauto

theorem completions_nil (square : Bool) (r : ℕ) (first : Bool) :
    completions square r first [] = [[]] := by
  cases r <;> simp [completions]

theorem mem_completions_nil (square : Bool) (r : ℕ) (first : Bool) (q : List Placement) :
    q ∈ completions square r first [] ↔ q = [] := by
  simp [completions_nil]

theorem nil_not_mem_completions (square : Bool) (r : ℕ) (first : Bool) {s : List (Tier Unit)}
    (hs : s ≠ []) : [] ∉ completions square r first s := by
  rw [mem_completions]
  rintro ⟨h, -⟩
  exact hs h

theorem moves_zero (square : Bool) (s : List (Tier Unit)) (first : Bool) :
    moves square s 0 first = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro mv hmv
  exact absurd ((mem_moves _ _ _ _ _).mp hmv).1.2.1 (lt_irrefl 0)

theorem completions_cons (square : Bool) (r : ℕ) (first : Bool) (t : Tier Unit)
    (s : List (Tier Unit)) :
    completions square r first (t :: s) =
      (moves square (t :: s) r first).flatMap fun mv =>
        (completions square (r - 1) false (place unitAlgebra (t :: s) mv ())).map fun p =>
          mv :: p := by
  cases r with
  | zero => simp [completions, moves_zero]
  | succ r => simp [completions]

theorem nodup_candidates (count : ℕ) : (candidates count).Nodup := by
  rw [candidates, List.nodup_flatMap]
  refine ⟨fun tier _ => by simp [fits], List.nodup_range.imp ?_⟩
  intro i j hij
  rw [Function.onFun, List.disjoint_left]
  intro mv hi hj
  have h1 : mv.tier = i := by
    simp only [fits, List.mem_flatMap, List.mem_map] at hi
    obtain ⟨_, -, _, -, rfl⟩ := hi
    rfl
  have h2 : mv.tier = j := by
    simp only [fits, List.mem_flatMap, List.mem_map] at hj
    obtain ⟨_, -, _, -, rfl⟩ := hj
    rfl
  exact hij (h1.symm.trans h2)

theorem nodup_moves (square : Bool) (s : List (Tier Unit)) (remaining : ℕ) (first : Bool) :
    (moves square s remaining first).Nodup :=
  (nodup_candidates _).filter _

/-- No sequence is enumerated twice below a staircase. -/
theorem nodup_completions (square : Bool) :
    ∀ (r : ℕ) (first : Bool) (s : List (Tier Unit)), (completions square r first s).Nodup := by
  intro r
  induction r with
  | zero =>
    intro first s
    cases s <;> simp [completions]
  | succ r ih =>
    intro first s
    cases s with
    | nil => simp [completions]
    | cons t s =>
      rw [completions_cons, List.nodup_flatMap]
      refine ⟨fun mv _ => (ih _ _).map fun p q h => (List.cons.inj h).2,
        (nodup_moves _ _ _ _).imp ?_⟩
      intro mv mv' hne
      rw [Function.onFun, List.disjoint_left]
      intro p h h'
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
      obtain ⟨_, -, heq⟩ := List.mem_map.mp h'
      exact hne (List.cons.inj heq).1.symm

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
        simp [completions, moves_zero]
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

/-! ### The fallback within a prefix -/

/-- The complete sequences below a staircase that follow the given placements as far as these go, as in `Engine::delegate_rec`. -/
def forcedCompletions (square : Bool) :
    List Placement → ℕ → Bool → List (Tier Unit) → List (List Placement)
  | [], r, first, s => completions square r first s
  | f :: fs, r, first, s =>
    if s.isEmpty then [[]]
    else if f ∈ moves square s r first then
      (forcedCompletions square fs (r - 1) false (place unitAlgebra s f ())).map fun p => f :: p
    else []

theorem forcedCompletions_nil (square : Bool) (fs : List Placement) (r : ℕ) (first : Bool) :
    forcedCompletions square fs r first [] = [[]] := by
  cases fs <;> simp [forcedCompletions, completions_nil]

/-- The sequences enumerated when placements are forced are the enumerated sequences that begin with the forced placements, or that end before these do. -/
theorem mem_forcedCompletions (square : Bool) :
    ∀ (fs : List Placement) (r : ℕ) (first : Bool) (s : List (Tier Unit)) (p : List Placement),
      p ∈ forcedCompletions square fs r first s ↔
        p ∈ completions square r first s ∧ (fs <+: p ∨ p <+: fs) := by
  intro fs
  induction fs with
  | nil =>
    intro r first s p
    simp [forcedCompletions]
  | cons f fs ih =>
    intro r first s p
    rw [forcedCompletions]
    cases s with
    | nil =>
      rw [mem_completions_nil]
      constructor
      · rintro h
        obtain rfl : p = [] := by simpa using h
        simp
      · rintro ⟨rfl, -⟩
        simp
    | cons t s =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      cases p with
      | nil =>
        have hnil := nil_not_mem_completions square r first (List.cons_ne_nil t s)
        by_cases hf : f ∈ moves square (t :: s) r first <;> simp [hf, hnil]
      | cons mv q =>
        rw [cons_mem_completions_iff, List.cons_prefix_cons, List.cons_prefix_cons]
        by_cases hf : f ∈ moves square (t :: s) r first
        · simp only [hf, ↓reduceIte, List.mem_map, List.cons.injEq, exists_eq_right_right, ih]
          constructor
          · rintro ⟨⟨hq, hpre⟩, rfl⟩
            exact ⟨⟨hf, hq⟩, hpre.imp (fun h => ⟨rfl, h⟩) fun h => ⟨rfl, h⟩⟩
          · rintro ⟨⟨-, hq⟩, ⟨rfl, hpre⟩ | ⟨rfl, hpre⟩⟩
            · exact ⟨⟨hq, .inl hpre⟩, rfl⟩
            · exact ⟨⟨hq, .inr hpre⟩, rfl⟩
        · simp only [hf, ↓reduceIte, List.not_mem_nil, false_iff]
          rintro ⟨⟨hmv, -⟩, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
          · exact hf hmv
          · exact hf hmv

/-- **The fallback within the prefixes splits the enumeration.** The sequences enumerated with the placements of each prefix forced, taken over the prefixes in order, are the sequences enumerated below the staircase, each as often and in the same order. -/
theorem flatMap_forcedCompletions (square : Bool) :
    ∀ (d r : ℕ) (first : Bool) (s : List (Tier Unit)),
      ((prefixes square d r first s).flatMap fun pre => forcedCompletions square pre r first s) =
        completions square r first s := by
  intro d
  induction d with
  | zero =>
    intro r first s
    simp [prefixes, forcedCompletions]
  | succ d ih =>
    intro r first s
    rw [prefixes]
    cases s with
    | nil => simp [forcedCompletions, completions_nil]
    | cons t s =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [completions_cons, List.flatMap_assoc]
      refine List.flatMap_congr fun mv hmv => ?_
      rw [List.flatMap_map, ← ih (r - 1) false, List.map_flatMap]
      refine List.flatMap_congr fun pre _ => ?_
      simp [forcedCompletions, hmv]

end Rectiling
