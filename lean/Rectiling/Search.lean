-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Fast
import Rectiling.Enumeration

/-!
# The search by the default method

Model of the depth-first search of `src/fast.rs` and of its driver in `src/search.rs`: `Engine::explore` below a stage, the passage of a whole subtree to the reference method when the symbolic pass fails (`Engine::delegate`), and the splitting of the search by forced prefixes (`Search::run` and `Engine::run`).
The proportions found by the search are those of `FastReported`.
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

/-- The proportions found below a stage when the first placements are forced, as in `Engine::explore` with a prefix; a failure of the symbolic pass on a forced placement passes the whole subtree below it to the reference method. -/
noncomputable def exploreForced (square : Bool) :
    List Placement → ℕ → Stage Coeff → List Placement → List (Step Coeff) → ℝ → Prop
  | [], r, st, done, sd => explore M P N a b square r st done sd
  | f :: fs, r, st, done, sd => fun x =>
    f ∈ moves square (flags st.stairs) r done.isEmpty ∧
      match advance M st done f with
      | .fail =>
        ∃ q ∈ completions square (r - 1) false (place unitAlgebra (flags st.stairs) f ()),
          x ∈ (solve P a b (done ++ f :: q)).feasible
      | .final step E =>
        x ∈ (match leaf P N a b (done ++ [f]) (sd ++ [step]) E with
          | some S => S
          | none => (solve P a b (done ++ [f])).feasible)
      | .next st' step => exploreForced square fs (r - 1) st' (done ++ [f]) (sd ++ [step]) x

/-- The proportions found by the search for `n` tiles, split by the prefixes of length at most `d`, as in `Search::run`. -/
def Searched (d n : ℕ) (x : ℝ) : Prop :=
  ∃ pre ∈ prefixes (decide (a = b)) d n true (initial () ()),
    exploreForced M P N a b (decide (a = b)) pre n (Stage.init a b) [] [] x

variable {M P N a b}

theorem isEmpty_concat (done : List Placement) (mv : Placement) :
    (done ++ [mv]).isEmpty = false := by
  cases done <;> rfl

theorem cons_mem_completions_iff (square : Bool) (r : ℕ) (first : Bool) (s : List (Tier Unit))
    (mv : Placement) (q : List Placement) :
    (mv :: q) ∈ completions square r first s ↔
      mv ∈ moves square s r first ∧
        q ∈ completions square (r - 1) false (place unitAlgebra s mv ()) := by
  rw [mem_completions, mem_moves, mem_completions]
  simp only [CompleteFrom, FirstWide, List.head?_cons, Option.mem_def, Option.some.injEq,
    forall_eq', Bool.false_eq_true, false_implies, and_true]
  tauto

theorem mem_completions_nil (square : Bool) (r : ℕ) (first : Bool) (q : List Placement) :
    q ∈ completions square r first [] ↔ q = [] := by
  cases r <;> simp [completions]

theorem nil_not_mem_completions (square : Bool) (r : ℕ) (first : Bool) {s : List (Tier Unit)}
    (hs : s ≠ []) : [] ∉ completions square r first s := by
  rw [mem_completions]
  rintro ⟨h, -⟩
  exact hs h

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
      exact ⟨fs ++ q, hq', hx⟩
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

end Tree

end Fast

end Rectiling
