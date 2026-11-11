-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Fast
import Rectiling.Enumeration

/-!
# The search by the default method

Model of the depth-first search of `src/fast.rs` and of its driver in `src/search.rs`: `Engine::explore` below a stage, the passage of a subtree to the reference method when the symbolic pass fails (`Engine::delegate`), which keeps to the forced placements still to be followed, and the splitting of the search by forced prefixes (`Search::run` and `Engine::run`).
The proportions found by the search are those of `FastReported`, and every complete sequence is examined once, under one prefix.
-/

namespace Rectiling

namespace Fast

/-- The staircase without its lengths. -/
def flags (s : List (Tier (Vec Coeff))) : List (Tier Unit) :=
  s.map (Tier.map fun _ => ())

theorem flags_place (s : List (Tier (Vec Coeff))) (mv : Placement) (side : Vec Coeff) :
    flags (place (vecAlgebra propX) s mv side) = place unitAlgebra (flags s) mv () :=
  place_map (Algebra.isHom_unit _) s mv side

theorem flags_map (f : Vec Coeff → Vec Coeff) (s : List (Tier (Vec Coeff))) :
    flags (s.map (Tier.map f)) = flags s := by
  simp only [flags, List.map_map]
  rfl

section Tree

variable (M : Limits) (P : Primitives) (N : Numerics) (a b : ℤ)

/-- The proportions reported for a complete sequence below a stage, given the placements already made and their records. -/
noncomputable def below (st : Stage Coeff) (done : List Placement) (sd : List (Step Coeff))
    (p : List Placement) : Finset ℝ :=
  match run M st done p with
  | none => (solve P a b (done ++ p)).feasible
  | some r =>
    match leaf P N a b (done ++ p) (sd ++ r.1) r.2 with
    | some S => S
    | none => (solve P a b (done ++ p)).feasible

theorem fastSolve_eq_below (path : List Placement) :
    fastSolve M P N a b path = below M P N a b (Stage.init a b) [] [] path := by
  unfold fastSolve direct below
  cases run M (Stage.init a b) [] path with
  | none => rfl
  | some r => rfl

variable {M P N a b}

theorem below_fail {st : Stage Coeff} {done : List Placement} {mv : Placement}
    (h : advance M st done mv = .fail) (sd : List (Step Coeff)) (q : List Placement) :
    below M P N a b st done sd (mv :: q) = (solve P a b (done ++ mv :: q)).feasible := by
  simp [below, run, h]

theorem below_final {st : Stage Coeff} {done : List Placement} {mv : Placement}
    {step : Step Coeff} {E : Vec Coeff} (h : advance M st done mv = .final step E)
    (sd : List (Step Coeff)) :
    below M P N a b st done sd [mv] =
      match leaf P N a b (done ++ [mv]) (sd ++ [step]) E with
      | some S => S
      | none => (solve P a b (done ++ [mv])).feasible := by
  simp [below, run, h]

theorem below_next {st st' : Stage Coeff} {done : List Placement} {mv : Placement}
    {step : Step Coeff} (h : advance M st done mv = .next st' step) (sd : List (Step Coeff))
    (q : List Placement) :
    below M P N a b st done sd (mv :: q) =
      below M P N a b st' (done ++ [mv]) (sd ++ [step]) q := by
  simp only [below, run, h]
  cases run M st' (done ++ [mv]) q <;> simp

variable (M P N a b)

/-- The proportions found below a stage with the given number of tiles still to place, as in `Engine::explore`; a subtree on which the symbolic pass fails is enumerated and passed to the reference method, as in `Engine::delegate`. -/
noncomputable def explore (square : Bool) :
    ℕ → Stage Coeff → List Placement → List (Step Coeff) → ℝ → Prop
  | 0, _, _, _ => fun _ => False
  | r + 1, st, done, sd => fun x =>
    ∃ mv ∈ moves square (flags st.stairs) (r + 1) done.isEmpty,
      match advance M st done mv with
      | .fail =>
        ∃ q ∈ completions square r false (place unitAlgebra (flags st.stairs) mv ()),
          x ∈ (solve P a b (done ++ mv :: q)).feasible
      | .final step E =>
        x ∈ (match leaf P N a b (done ++ [mv]) (sd ++ [step]) E with
          | some S => S
          | none => (solve P a b (done ++ [mv])).feasible)
      | .next st' step => explore square r st' (done ++ [mv]) (sd ++ [step]) x

/-- The proportions found below a stage when the first placements are forced, as in `Engine::explore` with a prefix; after a failure of the symbolic pass on a forced placement, the reference method receives the sequences below it that follow the forced placements still to come, as in `Engine::delegate` with a prefix. -/
noncomputable def exploreForced (square : Bool) :
    List Placement → ℕ → Stage Coeff → List Placement → List (Step Coeff) → ℝ → Prop
  | [], r, st, done, sd => explore M P N a b square r st done sd
  | f :: fs, r, st, done, sd => fun x =>
    f ∈ moves square (flags st.stairs) r done.isEmpty ∧
      match advance M st done f with
      | .fail =>
        ∃ q ∈ forcedCompletions square fs (r - 1) false
            (place unitAlgebra (flags st.stairs) f ()),
          x ∈ (solve P a b (done ++ f :: q)).feasible
      | .final step E =>
        x ∈ (match leaf P N a b (done ++ [f]) (sd ++ [step]) E with
          | some S => S
          | none => (solve P a b (done ++ [f])).feasible)
      | .next st' step => exploreForced square fs (r - 1) st' (done ++ [f]) (sd ++ [step]) x

/-- The complete sequences examined below a stage, in the order of `explore` and each as often as it is examined. -/
noncomputable def examined (square : Bool) :
    ℕ → Stage Coeff → List Placement → List (List Placement)
  | 0, _, _ => []
  | r + 1, st, done =>
    (moves square (flags st.stairs) (r + 1) done.isEmpty).flatMap fun mv =>
      match advance M st done mv with
      | .fail =>
        (completions square r false (place unitAlgebra (flags st.stairs) mv ())).map fun q =>
          mv :: q
      | .final _ _ => [[mv]]
      | .next st' _ => (examined square r st' (done ++ [mv])).map fun q => mv :: q

/-- The complete sequences examined below a stage when the first placements are forced, in the order of `exploreForced` and each as often as it is examined. -/
noncomputable def examinedForced (square : Bool) :
    List Placement → ℕ → Stage Coeff → List Placement → List (List Placement)
  | [], r, st, done => examined M square r st done
  | f :: fs, r, st, done =>
    if f ∈ moves square (flags st.stairs) r done.isEmpty then
      match advance M st done f with
      | .fail =>
        (forcedCompletions square fs (r - 1) false
          (place unitAlgebra (flags st.stairs) f ())).map fun q => f :: q
      | .final _ _ => [[f]]
      | .next st' _ => (examinedForced square fs (r - 1) st' (done ++ [f])).map fun q => f :: q
    else []

/-- The proportions found by the search for `n` tiles, split by the prefixes of length at most `d`, as in `Search::run`. -/
def Searched (d n : ℕ) (x : ℝ) : Prop :=
  ∃ pre ∈ prefixes (decide (a = b)) d n true (initial () ()),
    exploreForced M P N a b (decide (a = b)) pre n (Stage.init a b) [] [] x

variable {M P N a b}

theorem isEmpty_concat (done : List Placement) (mv : Placement) :
    (done ++ [mv]).isEmpty = false := by
  cases done <;> rfl

theorem flags_next {st st' : Stage Coeff} {done : List Placement} {mv : Placement}
    {step : Step Coeff} (h : advance M st done mv = .next st' step) :
    st'.stairs ≠ [] ∧ flags st'.stairs = place unitAlgebra (flags st.stairs) mv () := by
  obtain ⟨hne, hcase⟩ := advance_next h
  rcases hcase with ⟨size, -, -, -, rfl⟩ | ⟨size, E, m, -, -, -, -, -, -, -, rfl⟩
  · exact ⟨hne, flags_place _ _ _⟩
  · refine ⟨?_, ?_⟩
    · simpa using hne
    · simp only [flags_map]
      exact flags_place _ _ _

/-- **The search below a stage.** The proportions found below a stage are those reported for the complete sequences enumerated below it. -/
theorem explore_iff (square : Bool) :
    ∀ (r : ℕ) (st : Stage Coeff) (done : List Placement) (sd : List (Step Coeff)) (x : ℝ),
      st.stairs ≠ [] →
      (explore M P N a b square r st done sd x ↔
        ∃ p ∈ completions square r done.isEmpty (flags st.stairs),
          x ∈ below M P N a b st done sd p) := by
  intro r
  induction r with
  | zero =>
    intro st done sd x hne
    have hf : flags st.stairs ≠ [] := by simpa [flags] using hne
    cases hfs : flags st.stairs with
    | nil => exact absurd hfs hf
    | cons t s => simp [explore, completions]
  | succ r ih =>
    intro st done sd x hne
    have hf : flags st.stairs ≠ [] := by simpa [flags] using hne
    rw [explore]
    constructor
    · rintro ⟨mv, hmv, h⟩
      cases hadv : advance M st done mv with
      | fail =>
        rw [hadv] at h
        obtain ⟨q, hq, hx⟩ := h
        exact ⟨mv :: q, (cons_mem_completions_iff _ _ _ _ _ _).mpr ⟨hmv, hq⟩, by
          rw [below_fail hadv]
          exact hx⟩
      | final step E =>
        rw [hadv] at h
        obtain ⟨-, -, -, -, hempty⟩ := advance_final hadv
        refine ⟨[mv], (cons_mem_completions_iff _ _ _ _ _ _).mpr ⟨hmv, ?_⟩, by
          rw [below_final hadv]
          exact h⟩
        rw [← flags_place (side := st.side), hempty]
        exact (mem_completions_nil _ _ _ _).mpr rfl
      | next st' step =>
        rw [hadv] at h
        obtain ⟨hne', hfl⟩ := flags_next hadv
        obtain ⟨q, hq, hx⟩ := (ih st' _ _ x hne').mp h
        rw [isEmpty_concat] at hq
        refine ⟨mv :: q, (cons_mem_completions_iff _ _ _ _ _ _).mpr ⟨hmv, ?_⟩, by
          rw [below_next hadv]
          exact hx⟩
        rw [← hfl]
        exact hq
    · rintro ⟨p, hp, hx⟩
      cases p with
      | nil => exact absurd hp (nil_not_mem_completions _ _ _ hf)
      | cons mv q =>
        obtain ⟨hmv, hq⟩ := (cons_mem_completions_iff _ _ _ _ _ _).mp hp
        refine ⟨mv, hmv, ?_⟩
        cases hadv : advance M st done mv with
        | fail =>
          rw [below_fail hadv] at hx
          exact ⟨q, hq, hx⟩
        | final step E =>
          obtain ⟨-, -, -, -, hempty⟩ := advance_final hadv
          rw [← flags_place (side := st.side), hempty] at hq
          obtain rfl := (mem_completions_nil _ _ _ _).mp hq
          rw [below_final hadv] at hx
          exact hx
        | next st' step =>
          obtain ⟨hne', hfl⟩ := flags_next hadv
          rw [below_next hadv] at hx
          refine (ih st' _ _ x hne').mpr ⟨q, ?_, hx⟩
          rw [hfl, isEmpty_concat]
          exact hq

/-- Everything found with forced placements is reported for an enumerated sequence. -/
theorem exploreForced_sub (square : Bool) :
    ∀ (fs : List Placement) (r : ℕ) (st : Stage Coeff) (done : List Placement)
      (sd : List (Step Coeff)) (x : ℝ), st.stairs ≠ [] →
      exploreForced M P N a b square fs r st done sd x →
      ∃ p ∈ completions square r done.isEmpty (flags st.stairs),
        x ∈ below M P N a b st done sd p := by
  intro fs
  induction fs with
  | nil =>
    intro r st done sd x hne h
    exact (explore_iff square r st done sd x hne).mp h
  | cons f fs ih =>
    intro r st done sd x hne h
    rw [exploreForced] at h
    obtain ⟨hmv, h⟩ := h
    cases hadv : advance M st done f with
    | fail =>
      rw [hadv] at h
      obtain ⟨q, hq, hx⟩ := h
      replace hq := ((mem_forcedCompletions _ _ _ _ _ _).mp hq).1
      exact ⟨f :: q, (cons_mem_completions_iff _ _ _ _ _ _).mpr ⟨hmv, hq⟩, by
        rw [below_fail hadv]
        exact hx⟩
    | final step E =>
      rw [hadv] at h
      obtain ⟨-, -, -, -, hempty⟩ := advance_final hadv
      refine ⟨[f], (cons_mem_completions_iff _ _ _ _ _ _).mpr ⟨hmv, ?_⟩, by
        rw [below_final hadv]
        exact h⟩
      rw [← flags_place (side := st.side), hempty]
      exact (mem_completions_nil _ _ _ _).mpr rfl
    | next st' step =>
      rw [hadv] at h
      obtain ⟨hne', hfl⟩ := flags_next hadv
      obtain ⟨q, hq, hx⟩ := ih _ st' _ _ x hne' h
      rw [isEmpty_concat] at hq
      refine ⟨f :: q, (cons_mem_completions_iff _ _ _ _ _ _).mpr ⟨hmv, ?_⟩, by
        rw [below_next hadv]
        exact hx⟩
      rw [← hfl]
      exact hq

/-- Everything reported for an enumerated sequence is found when a prefix of the sequence is forced. -/
theorem exploreForced_sup (square : Bool) :
    ∀ (fs : List Placement) (r : ℕ) (st : Stage Coeff) (done : List Placement)
      (sd : List (Step Coeff)) (x : ℝ) (q : List Placement), st.stairs ≠ [] →
      (fs ++ q) ∈ completions square r done.isEmpty (flags st.stairs) →
      x ∈ below M P N a b st done sd (fs ++ q) →
      exploreForced M P N a b square fs r st done sd x := by
  intro fs
  induction fs with
  | nil =>
    intro r st done sd x q hne hq hx
    exact (explore_iff square r st done sd x hne).mpr ⟨q, hq, hx⟩
  | cons f fs ih =>
    intro r st done sd x q hne hq hx
    rw [exploreForced]
    rw [List.cons_append] at hq hx
    obtain ⟨hmv, hq'⟩ := (cons_mem_completions_iff _ _ _ _ _ _).mp hq
    refine ⟨hmv, ?_⟩
    cases hadv : advance M st done f with
    | fail =>
      rw [below_fail hadv] at hx
      exact ⟨fs ++ q, (mem_forcedCompletions _ _ _ _ _ _).mpr ⟨hq', .inl (List.prefix_append _ _)⟩,
        hx⟩
    | final step E =>
      obtain ⟨-, -, -, -, hempty⟩ := advance_final hadv
      rw [← flags_place (side := st.side), hempty] at hq'
      have hnil := (mem_completions_nil _ _ _ _).mp hq'
      rw [hnil, below_final hadv] at hx
      exact hx
    | next st' step =>
      obtain ⟨hne', hfl⟩ := flags_next hadv
      rw [below_next hadv] at hx
      refine ih _ st' _ _ x q hne' ?_ hx
      rw [hfl, isEmpty_concat]
      exact hq'

/-- **The search finds the reported proportions.** Whatever the length of the prefixes by which the search is split, the proportions found by the depth-first search are those reported by the default method for the complete admissible sequences, with the first tile wide for a square. -/
theorem searched_iff (d n : ℕ) (x : ℝ) :
    Searched M P N a b d n x ↔ FastReported M P N a b n x := by
  have hinit : flags (Stage.init a b : Stage Coeff).stairs = initial () () := rfl
  have hne : (Stage.init a b : Stage Coeff).stairs ≠ [] := by simp [Stage.init, homInitial, initial]
  constructor
  · rintro ⟨pre, -, h⟩
    obtain ⟨p, hp, hx⟩ := exploreForced_sub _ pre n _ [] [] x hne h
    rw [hinit] at hp
    obtain ⟨hcomplete, hwide⟩ := (mem_completions_initial _ n p).mp hp
    rw [← fastSolve_eq_below] at hx
    exact ⟨p, hcomplete, fun hab => hwide (by simpa using hab), hx⟩
  · rintro ⟨p, hcomplete, hwide, hx⟩
    have hp : p ∈ completions (decide (a = b)) n true (initial () ()) :=
      (mem_completions_initial _ n p).mpr ⟨hcomplete, fun hab => hwide (by simpa using hab)⟩
    obtain ⟨pre, hpre, q, rfl, -⟩ := (mem_completions_iff_prefix _ d n true _ p).mp hp
    refine ⟨pre, hpre, exploreForced_sup _ pre n _ [] [] x q hne ?_ ?_⟩
    · rw [hinit]
      exact hp
    · rw [← fastSolve_eq_below]
      exact hx

/-! ### The sequences examined -/

/-- The proportions found below a stage are those reported for the sequences examined below it. -/
theorem explore_iff_examined (square : Bool) :
    ∀ (r : ℕ) (st : Stage Coeff) (done : List Placement) (sd : List (Step Coeff)) (x : ℝ),
      explore M P N a b square r st done sd x ↔
        ∃ p ∈ examined M square r st done, x ∈ below M P N a b st done sd p := by
  intro r
  induction r with
  | zero =>
    intro st done sd x
    simp [explore, examined]
  | succ r ih =>
    intro st done sd x
    rw [explore, examined]
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨mv, hmv, h⟩
      cases hadv : advance M st done mv with
      | fail =>
        rw [hadv] at h
        obtain ⟨q, hq, hx⟩ := h
        refine ⟨mv :: q, ⟨mv, hmv, ?_⟩, by
          rw [below_fail hadv]
          exact hx⟩
        rw [hadv]
        exact List.mem_map.mpr ⟨q, hq, rfl⟩
      | final step E =>
        rw [hadv] at h
        refine ⟨[mv], ⟨mv, hmv, ?_⟩, by
          rw [below_final hadv]
          exact h⟩
        rw [hadv]
        exact List.mem_singleton.mpr rfl
      | next st' step =>
        rw [hadv] at h
        obtain ⟨q, hq, hx⟩ := (ih st' _ _ x).mp h
        refine ⟨mv :: q, ⟨mv, hmv, ?_⟩, by
          rw [below_next hadv]
          exact hx⟩
        rw [hadv]
        exact List.mem_map.mpr ⟨q, hq, rfl⟩
    · rintro ⟨p, ⟨mv, hmv, hp⟩, hx⟩
      refine ⟨mv, hmv, ?_⟩
      cases hadv : advance M st done mv with
      | fail =>
        rw [hadv] at hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        rw [below_fail hadv] at hx
        exact ⟨q, hq, hx⟩
      | final step E =>
        rw [hadv] at hp
        obtain rfl := List.mem_singleton.mp hp
        rw [below_final hadv] at hx
        exact hx
      | next st' step =>
        rw [hadv] at hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        rw [below_next hadv] at hx
        exact (ih st' _ _ x).mpr ⟨q, hq, hx⟩

/-- The proportions found with forced placements are those reported for the sequences examined. -/
theorem exploreForced_iff_examined (square : Bool) :
    ∀ (fs : List Placement) (r : ℕ) (st : Stage Coeff) (done : List Placement)
      (sd : List (Step Coeff)) (x : ℝ),
      exploreForced M P N a b square fs r st done sd x ↔
        ∃ p ∈ examinedForced M square fs r st done, x ∈ below M P N a b st done sd p := by
  intro fs
  induction fs with
  | nil =>
    intro r st done sd x
    exact explore_iff_examined square r st done sd x
  | cons f fs ih =>
    intro r st done sd x
    rw [exploreForced, examinedForced]
    by_cases hmv : f ∈ moves square (flags st.stairs) r done.isEmpty
    · simp only [hmv, true_and, ↓reduceIte]
      cases hadv : advance M st done f with
      | fail =>
        simp only [List.mem_map]
        constructor
        · rintro ⟨q, hq, hx⟩
          exact ⟨f :: q, ⟨q, hq, rfl⟩, by
            rw [below_fail hadv]
            exact hx⟩
        · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩
          rw [below_fail hadv] at hx
          exact ⟨q, hq, hx⟩
      | final step E =>
        simp only [List.mem_singleton, exists_eq_left, below_final hadv]
      | next st' step =>
        simp only [List.mem_map]
        rw [ih]
        constructor
        · rintro ⟨q, hq, hx⟩
          exact ⟨f :: q, ⟨q, hq, rfl⟩, by
            rw [below_next hadv]
            exact hx⟩
        · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩
          rw [below_next hadv] at hx
          exact ⟨q, hq, hx⟩
    · simp [hmv]

/-- The sequences examined below a stage are those enumerated below its staircase, each as often and in the same order. -/
theorem examined_eq (square : Bool) :
    ∀ (r : ℕ) (st : Stage Coeff) (done : List Placement), st.stairs ≠ [] →
      examined M square r st done = completions square r done.isEmpty (flags st.stairs) := by
  intro r
  induction r with
  | zero =>
    intro st done hne
    have hf : flags st.stairs ≠ [] := by simpa [flags] using hne
    cases hfs : flags st.stairs with
    | nil => exact absurd hfs hf
    | cons t s => simp [examined, completions]
  | succ r ih =>
    intro st done hne
    have hf : flags st.stairs ≠ [] := by simpa [flags] using hne
    rw [examined]
    obtain ⟨t, s, hfs⟩ := List.exists_cons_of_ne_nil hf
    rw [hfs, completions_cons, ← hfs]
    refine List.flatMap_congr fun mv _ => ?_
    simp only [Nat.add_sub_cancel]
    cases hadv : advance M st done mv with
    | fail => rfl
    | final step E =>
      obtain ⟨-, -, -, -, hempty⟩ := advance_final hadv
      rw [← flags_place (side := st.side), hempty]
      simp [flags, completions_nil]
    | next st' step =>
      obtain ⟨hne', hfl⟩ := flags_next hadv
      simp only [ih st' _ hne', isEmpty_concat, hfl]

/-- The sequences examined with forced placements are those that the fallback enumerates with the same placements forced, each as often and in the same order. -/
theorem examinedForced_eq (square : Bool) :
    ∀ (fs : List Placement) (r : ℕ) (st : Stage Coeff) (done : List Placement), st.stairs ≠ [] →
      examinedForced M square fs r st done =
        forcedCompletions square fs r done.isEmpty (flags st.stairs) := by
  intro fs
  induction fs with
  | nil =>
    intro r st done hne
    exact examined_eq square r st done hne
  | cons f fs ih =>
    intro r st done hne
    have hf : flags st.stairs ≠ [] := by simpa [flags] using hne
    rw [examinedForced, forcedCompletions]
    obtain ⟨t, s, hfs⟩ := List.exists_cons_of_ne_nil hf
    have hne' : (flags st.stairs).isEmpty = false := by simp [hfs]
    simp only [hne', Bool.false_eq_true, ↓reduceIte]
    by_cases hmv : f ∈ moves square (flags st.stairs) r done.isEmpty
    · simp only [hmv, ↓reduceIte]
      cases hadv : advance M st done f with
      | fail => rfl
      | final step E =>
        obtain ⟨-, -, -, -, hempty⟩ := advance_final hadv
        rw [← flags_place (side := st.side), hempty]
        simp [flags, forcedCompletions_nil]
      | next st' step =>
        obtain ⟨hne'', hfl⟩ := flags_next hadv
        simp only [ih _ st' _ hne'', isEmpty_concat, hfl]
    · simp only [hmv, ↓reduceIte]

/-- **The prefixes split the search.** The sequences examined under the prefixes of length at most `d`, taken in order, are the sequences enumerated for `n` tiles, each as often and in the same order. -/
theorem examined_split (square : Bool) (d n : ℕ) :
    ((prefixes square d n true (initial () ())).flatMap fun pre =>
      examinedForced M square pre n (Stage.init a b) []) =
        completions square n true (initial () ()) := by
  have hinit : flags (Stage.init a b : Stage Coeff).stairs = initial () () := rfl
  have hne : (Stage.init a b : Stage Coeff).stairs ≠ [] := by simp [Stage.init, homInitial, initial]
  rw [← flatMap_forcedCompletions square d n true]
  refine List.flatMap_congr fun pre _ => ?_
  rw [examinedForced_eq square pre n _ [] hne, hinit]
  rfl

/-- **Every sequence is examined once.** Whatever the length of the prefixes by which the search is split, a complete admissible sequence, with the first tile wide for a square, is examined once in all: the numbers of times that it is examined under the prefixes add up to one. -/
theorem examined_once (d n : ℕ) {p : List Placement} (hp : Complete n p)
    (hwide : a = b → FirstWide p) :
    ((prefixes (decide (a = b)) d n true (initial () ())).map fun pre =>
      (examinedForced M (decide (a = b)) pre n (Stage.init a b) []).count p).sum = 1 := by
  have h := List.count_flatMap (x := p) (l := prefixes (decide (a = b)) d n true (initial () ()))
    (f := fun pre => examinedForced M (decide (a = b)) pre n (Stage.init a b) [])
  rw [examined_split] at h
  rw [show (fun pre => (examinedForced M (decide (a = b)) pre n (Stage.init a b) []).count p) =
    List.count p ∘ fun pre => examinedForced M (decide (a = b)) pre n (Stage.init a b) [] from rfl,
    ← h]
  exact List.count_eq_one_of_mem (nodup_completions _ _ _ _)
    ((mem_completions_initial _ n p).mpr ⟨hp, fun hab => hwide (by simpa using hab)⟩)

/-- Only complete admissible sequences are examined, with the first tile wide for a square. -/
theorem examined_complete (d n : ℕ) {pre p : List Placement}
    (hpre : pre ∈ prefixes (decide (a = b)) d n true (initial () ()))
    (hp : p ∈ examinedForced M (decide (a = b)) pre n (Stage.init a b) []) :
    Complete n p ∧ (a = b → FirstWide p) := by
  have h : p ∈ completions (decide (a = b)) n true (initial () ()) := by
    rw [← examined_split (M := M) (a := a) (b := b)]
    exact List.mem_flatMap.mpr ⟨pre, hpre, hp⟩
  obtain ⟨hcomplete, hw⟩ := (mem_completions_initial _ n p).mp h
  exact ⟨hcomplete, fun hab => hw (by simpa using hab)⟩

end Tree

end Fast

end Rectiling
