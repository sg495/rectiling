-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Certified
import Rectiling.Main

/-!
# The default method

Model of the treatment of one complete placement sequence by `src/fast.rs`, and its specification: the proportions reported for the sequence without recourse to the reference method are exactly the real numbers `x ≥ 1` at which the emitted system has a solution satisfying every constraint, and every other case is passed to the reference method.

The symbolic pass fails, and the sequence is passed to the reference method, when an arithmetic operation exceeds the machine limits, when no unknown can be eliminated, or when a division is not exact.
The first two are not modelled: they enter through `Limits`, on which nothing is assumed.
-/

open Polynomial

namespace Rectiling

namespace Fast

/-- The machine limits and the choices of the symbolic pass, on which nothing is assumed. -/
structure Limits where
  /-- Whether an arithmetic operation fails while the last placement of the given sequence is treated. -/
  overflow : List Placement → Bool
  /-- The unknown chosen for elimination after the last placement of the given sequence, for the given equation, if any. -/
  pick : List Placement → Vec Coeff → Option ℕ

open Classical in
/-- The symbolic pass along a path from a stage, after the placements already made: the records of the placements and the final equation, or a failure. -/
noncomputable def run (M : Limits) :
    Stage Coeff → List Placement → List Placement → Option (List (Step Coeff) × Vec Coeff)
  | _, _, [] => none
  | st, done, mv :: rest =>
    if M.overflow (done ++ [mv]) then none
    else
      match positiveAt st.stairs mv st.side with
      | none => none
      | some size =>
        match equationAt (vecAlgebra propX) st.stairs mv with
        | none =>
          (run M ⟨place (vecAlgebra propX) st.stairs mv st.side, st.pivot,
            nextIndex st.count mv⟩ (done ++ [mv]) rest).map
              fun r => (⟨mv, size, none⟩ :: r.1, r.2)
        | some E =>
          if (place (vecAlgebra propX) st.stairs mv st.side).isEmpty then
            if rest.isEmpty then some ([⟨mv, size, none⟩], E) else none
          else
            match M.pick (done ++ [mv]) E with
            | none => none
            | some m =>
              if 1 ≤ m ∧ m ≤ nextIndex st.count mv ∧ E m ≠ 0 ∧
                  ∀ t ∈ place (vecAlgebra propX) st.stairs mv st.side,
                    Divisible (E, m, st.pivot) t.floor ∧ Divisible (E, m, st.pivot) t.wall then
                (run M ⟨(place (vecAlgebra propX) st.stairs mv st.side).map
                  (Tier.map (elimForm (E, m, st.pivot))), E m, nextIndex st.count mv⟩
                  (done ++ [mv]) rest).map
                    fun r => (⟨mv, size, some (E, m, st.pivot)⟩ :: r.1, r.2)
              else none

/-- A symbolic pass that does not fail is a successful pass in the sense of `Run`. -/
theorem run_spec (M : Limits) :
    ∀ (path : List Placement) (st : Stage Coeff) (done : List Placement)
      (steps : List (Step Coeff)) (E : Vec Coeff),
      run M st done path = some (steps, E) → Run propX st path steps E := by
  intro path
  induction path with
  | nil => intro st done steps E h; simp [run] at h
  | cons mv rest ih =>
    intro st done steps E h
    rw [run] at h
    by_cases hov : M.overflow (done ++ [mv]) = true
    · simp [hov] at h
    simp only [hov, Bool.false_eq_true, ↓reduceIte] at h
    cases hsize : positiveAt st.stairs mv st.side with
    | none => simp [hsize] at h
    | some size =>
      rw [hsize] at h
      simp only at h
      cases heq : equationAt (vecAlgebra propX) st.stairs mv with
      | none =>
        rw [heq] at h
        simp only at h
        obtain ⟨⟨steps', E'⟩, hr, hpair⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact Run.plain hsize heq (ih _ _ _ _ hr)
      | some Eq =>
        rw [heq] at h
        simp only at h
        by_cases hempty : (place (vecAlgebra propX) st.stairs mv st.side).isEmpty = true
        · simp only [hempty, ↓reduceIte] at h
          by_cases hrest : rest.isEmpty = true
          · simp only [hrest, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain rfl : rest = [] := List.isEmpty_iff.mp hrest
            exact Run.leaf hsize heq
          · simp [hrest] at h
        · simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h
          cases hpick : M.pick (done ++ [mv]) Eq with
          | none => simp [hpick] at h
          | some m =>
            rw [hpick] at h
            simp only at h
            split_ifs at h with hcond
            obtain ⟨hm1, hm, hEm, hdiv⟩ := hcond
            obtain ⟨⟨steps', E'⟩, hr, hpair⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at hpair
            obtain ⟨rfl, rfl⟩ := hpair
            exact Run.elim hsize heq hm1 hm hEm hdiv (ih _ _ _ _ hr)

/-! ### The leaves -/

/-- The test that discards a proportion polynomial: its expansion in `X - 1` has non-negative coefficients and positive constant term. -/
def FastNoRoot (p : ℤ[X]) : Prop :=
  (∀ i, 0 ≤ (p.comp (X + 1)).coeff i) ∧ 0 < (p.comp (X + 1)).coeff 0

theorem FastNoRoot.noRootTest {p : ℤ[X]} (h : FastNoRoot p) : NoRootTest p :=
  ⟨Or.inl h.1, h.2.ne'⟩

open Classical in
/-- The decision of a leaf from the records of its path and its final equation, as in `Engine::leaf` and `Engine::finish`: the proportions accepted, or nothing if the leaf is passed to the reference method. -/
noncomputable def leaf (P : Primitives) (N : Numerics) (a b : ℤ) (path : List Placement)
    (steps : List (Step Coeff)) (E : Vec Coeff) : Option (Finset ℝ) :=
  if E 0 = 0 ∨ ∃ j, 0 < j ∧ E j ≠ 0 then none
  else if FastNoRoot (N.key (E 0)) then some ∅
  else if ∃ r ∈ P.roots (N.key (E 0)), check N a b path steps r = .unsure then none
  else some ((P.roots (N.key (E 0))).filter fun r => check N a b path steps r = .accept)

/-- The proportions that the default method accepts for a path without recourse to the reference method, or nothing if the path is passed to the reference method. -/
noncomputable def direct (M : Limits) (P : Primitives) (N : Numerics) (a b : ℤ)
    (path : List Placement) : Option (Finset ℝ) :=
  match run M (Stage.init a b) [] path with
  | none => none
  | some r => leaf P N a b path r.1 r.2

/-- The proportions that the default method reports for a path, for a main rectangle of width `a` and height `b`. -/
noncomputable def fastSolve (M : Limits) (P : Primitives) (N : Numerics) (a b : ℤ)
    (path : List Placement) : Finset ℝ :=
  match direct M P N a b path with
  | some S => S
  | none => (solve P a b path).feasible

/-- The path is passed to the reference method. -/
def Delegated (M : Limits) (P : Primitives) (N : Numerics) (a b : ℤ) (path : List Placement) :
    Prop :=
  direct M P N a b path = none

/-- The system emitted by a path, for a main rectangle of width `a / b` and height one, has a solution satisfying every constraint at the proportion `x ≥ 1`. -/
def Solvable (a b : ℤ) (path : List Placement) (x : ℝ) : Prop :=
  1 ≤ x ∧ ∃ fresh : ℕ → ℝ, Satisfies x fresh (initial ((a : ℝ) / b) 1) 0 path

/-- A solution for the main rectangle of width `a / b` and height one is a solution of scale one for the main rectangle of sides `a` and `b`. -/
theorem solvable_iff {a b : ℤ} (hb : 0 < b) (path : List Placement) (x : ℝ) :
    (∃ fresh : ℕ → ℝ, Satisfies x fresh (initial ((a : ℝ) / b) 1) 0 path) ↔
      ∃ w : ℕ → ℝ, w 0 = 1 ∧
        Satisfies x (fun j => w (j + 1)) (initial (a : ℝ) (b : ℝ)) 0 path := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · rintro ⟨fresh, h⟩
    refine ⟨fun j => if j = 0 then 1 else b * fresh (j - 1), by simp, ?_⟩
    have h1 := (satisfies_scale hbR fresh (initial ((a : ℝ) / b) 1) 0 path).mpr h
    have h2 : (initial ((a : ℝ) / b) 1).map (Tier.map fun l => (b : ℝ) * l) =
        initial (a : ℝ) (b : ℝ) := by
      simp only [initial, List.map_cons, List.map_nil, Tier.map, mul_one]
      rw [mul_div_cancel₀ _ hbR.ne']
    rw [h2] at h1
    simpa using h1
  · rintro ⟨w, -, h⟩
    refine ⟨fun j => (b : ℝ)⁻¹ * w (j + 1), ?_⟩
    have h1 := (satisfies_scale (inv_pos.mpr hbR) (fun j => w (j + 1))
      (initial (a : ℝ) (b : ℝ)) 0 path).mpr h
    have h2 : (initial (a : ℝ) (b : ℝ)).map (Tier.map fun l => (b : ℝ)⁻¹ * l) =
        initial ((a : ℝ) / b) 1 := by
      simp only [initial, List.map_cons, List.map_nil, Tier.map]
      rw [inv_mul_cancel₀ hbR.ne', inv_mul_eq_div]
    rw [h2] at h1
    exact h1

section Spec

variable (P : Primitives) (N : Numerics) {a b : ℤ} {n : ℕ} {path : List Placement}

/-- **Specification of a leaf.** A leaf that is not passed to the reference method accepts exactly the proportions at which the system has a solution satisfying every constraint. -/
theorem leaf_spec (hb : 0 < b) (hpath : Complete n path) {steps : List (Step Coeff)}
    {E : Vec Coeff} (hrun : Run propX (Stage.init a b) path steps E) {S : Finset ℝ}
    (h : leaf P N a b path steps E = some S) (x : ℝ) : x ∈ S ↔ Solvable a b path x := by
  by_cases h1 : E 0 = 0 ∨ ∃ j, 0 < j ∧ E j ≠ 0
  · simp [leaf, h1] at h
  have hE0 : E 0 ≠ 0 := fun h0 => h1 (Or.inl h0)
  have hEj : ∀ j, 0 < j → E j = 0 := by
    intro j hj
    by_contra hne
    exact h1 (Or.inr ⟨j, hj, hne⟩)
  have hkey : N.key (E 0) ≠ 0 := N.key_ne_zero hE0
  -- a solution is a root of the proportion polynomial
  have hsol : Solvable a b path x → x ∈ P.roots (N.key (E 0)) := by
    rintro ⟨hx1, hfresh⟩
    obtain ⟨w, hw0, hw⟩ := (solvable_iff hb path x).mp hfresh
    have hx0 : x ≠ 0 := by linarith
    have hsat := satisfies_iff_hom (evalL (Units.mk0 x hx0)) propX a b path w hw0
    rw [evalL_propX] at hsat
    have hvan := hrun.final_vanishes (evalL (Units.mk0 x hx0)) hpath hw0 (hsat.mp hw).2
    exact (P.mem_roots _ hkey x).mpr ⟨hx1, (N.key_eval (E 0) (Units.mk0 x hx0)).mpr hvan⟩
  simp only [leaf, h1, ↓reduceIte] at h
  split_ifs at h with h2 h3
  · -- no root
    obtain rfl : ∅ = S := by simpa using h
    constructor
    · intro hx
      simp at hx
    · intro hx
      have hroot := (P.mem_roots _ hkey x).mp (hsol hx)
      exact absurd hroot.2 (h2.noRootTest.ne_zero hroot.1)
  · -- every root is settled
    obtain rfl : _ = S := by simpa using h
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hroot, hacc⟩
      obtain ⟨hx1, hzero⟩ := (P.mem_roots _ hkey x).mp hroot
      have hx0 : x ≠ 0 := by linarith
      have hxpos : 0 < ((Units.mk0 x hx0 : ℝˣ) : ℝ) := by
        simp only [Units.val_mk0]
        linarith
      obtain ⟨hmem, hstr⟩ := N.mem_rootIv _ x hkey hx1 hzero
      obtain ⟨v, hv0, hv⟩ := check_accept (x := Units.mk0 x hx0) hpath hrun hxpos hmem hstr hEj
        ((N.key_eval (E 0) (Units.mk0 x hx0)).mp hzero) hacc
      exact ⟨hx1, (solvable_iff hb path x).mpr ⟨v, hv0, hv⟩⟩
    · intro hx
      have hroot := hsol hx
      refine ⟨hroot, ?_⟩
      obtain ⟨hx1, hzero⟩ := (P.mem_roots _ hkey x).mp hroot
      have hx0 : x ≠ 0 := by linarith
      have hxpos : 0 < ((Units.mk0 x hx0 : ℝˣ) : ℝ) := by
        simp only [Units.val_mk0]
        linarith
      obtain ⟨hmem, hstr⟩ := N.mem_rootIv _ x hkey hx1 hzero
      obtain ⟨w, hw0, hw⟩ := (solvable_iff hb path x).mp hx.2
      cases hc : check N a b path steps x with
      | accept => rfl
      | reject =>
        exact absurd hw (check_reject (x := Units.mk0 x hx0) hpath hrun hxpos hmem hstr hc w hw0)
      | unsure => exact absurd ⟨x, hroot, hc⟩ h3

/-- **Specification of the direct treatment.** A path that is not passed to the reference method reports exactly the proportions at which its system has a solution satisfying every constraint. -/
theorem direct_spec (M : Limits) (hb : 0 < b) (hpath : Complete n path) {S : Finset ℝ}
    (h : direct M P N a b path = some S) (x : ℝ) : x ∈ S ↔ Solvable a b path x := by
  unfold direct at h
  cases hr : run M (Stage.init a b) [] path with
  | none => simp [hr] at h
  | some r =>
    rw [hr] at h
    obtain ⟨steps, E⟩ := r
    exact leaf_spec P N hb hpath (run_spec M path _ _ steps E hr) h x

/-- **Soundness of the default method on a path.** Every proportion reported for a complete admissible path is a real number `x ≥ 1` at which the system has a solution satisfying every constraint. -/
theorem fastSolve_sound (M : Limits) (hb : 0 < b) (hpath : Complete n path) {x : ℝ}
    (hx : x ∈ fastSolve M P N a b path) : Solvable a b path x := by
  unfold fastSolve at hx
  cases hd : direct M P N a b path with
  | none =>
    rw [hd] at hx
    exact solve_sound P hb.ne' hpath hx
  | some S =>
    rw [hd] at hx
    exact (direct_spec P N M hb hpath hd x).mp hx

/-- **Completeness of the default method on a path.** Every such `x` is reported, provided that, if the path is passed to the reference method, the reference method counts no singular situation and does not find the aspect ratio independent of the proportion. -/
theorem fastSolve_complete (M : Limits) (hb : 0 < b) (hpath : Complete n path)
    (hcert : Delegated M P N a b path →
      (solve P a b path).singular = 0 ∧ (solve P a b path).constant = false)
    {x : ℝ} (hx : Solvable a b path x) : x ∈ fastSolve M P N a b path := by
  unfold fastSolve
  cases hd : direct M P N a b path with
  | none =>
    obtain ⟨hs, hc⟩ := hcert hd
    obtain ⟨hx1, fresh, hsat⟩ := hx
    exact solve_complete P hb.ne' hpath hs hc hx1 hsat
  | some S => exact (direct_spec P N M hb hpath hd x).mpr hx

/-- The default method reports every proportion that the reference method reports for a path. -/
theorem solve_subset_fastSolve (M : Limits) (hb : 0 < b) (hpath : Complete n path) :
    (solve P a b path).feasible ⊆ fastSolve M P N a b path := by
  intro x hx
  unfold fastSolve
  cases hd : direct M P N a b path with
  | none => exact hx
  | some S => exact (direct_spec P N M hb hpath hd x).mpr (solve_sound P hb.ne' hpath hx)

/-- **Agreement of the two methods on a path.** If the reference method counts no singular situation on a complete admissible path and does not find the aspect ratio independent of the proportion, the default method reports the same proportions. -/
theorem fastSolve_eq_solve (M : Limits) (hb : 0 < b) (hpath : Complete n path)
    (hsing : (solve P a b path).singular = 0) (hconst : (solve P a b path).constant = false) :
    fastSolve M P N a b path = (solve P a b path).feasible := by
  ext x
  rw [solve_spec P hb.ne' hpath hsing hconst x]
  exact ⟨fastSolve_sound P N M hb hpath,
    fastSolve_complete P N M hb hpath fun _ => ⟨hsing, hconst⟩⟩

end Spec

/-! ### The search -/

/-- The proportion `x` is reported by the default method for `n` tiles and a main rectangle of width `a` and height `b`: some enumerated placement sequence realises it. -/
def FastReported (M : Limits) (P : Primitives) (N : Numerics) (a b : ℤ) (n : ℕ) (x : ℝ) : Prop :=
  ∃ path, Complete n path ∧ (a = b → FirstWide path) ∧ x ∈ fastSolve M P N a b path

/-- The search by the default method is certified: no enumerated placement sequence that is passed to the reference method is singular or has an aspect ratio that does not depend on the proportion. -/
def FastCertified (M : Limits) (P : Primitives) (N : Numerics) (a b : ℤ) (n : ℕ) : Prop :=
  ∀ path, Complete n path → (a = b → FirstWide path) → Delegated M P N a b path →
    (solve P a b path).singular = 0 ∧ (solve P a b path).constant = false

theorem Certified.fast {P : Primitives} {a b : ℤ} {n : ℕ} (h : Certified P a b n) (M : Limits)
    (N : Numerics) : FastCertified M P N a b n :=
  fun path hpath hwide _ => h path hpath hwide

section Main

variable (M : Limits) (P : Primitives) (N : Numerics) {a b : ℤ}

/-- **Soundness of the default method.** Every reported proportion is the proportion of a tiling of the `a × b` rectangle by `n` rectangles. -/
theorem fast_sound (hb : 0 < b) {n : ℕ} {x : ℝ} (h : FastReported M P N a b n x) :
    ∃ tl : List Rect, IsSimilarTiling x (Rect.main a b) tl ∧ tl.length = n := by
  obtain ⟨path, hpath, -, hx⟩ := h
  obtain ⟨hx1, fresh, hsat⟩ := fastSolve_sound P N M hb hpath hx
  obtain ⟨htiling, hlen⟩ := soundness fresh hx1 hpath hsat
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hscaled := htiling.scale hbR
  rw [Rect.scale_main, mul_one, mul_div_cancel₀ _ hbR.ne'] at hscaled
  exact ⟨_, hscaled, by rw [List.length_map, hlen]⟩

/-- **Completeness of the default method.** If the search is certified, the proportion of every tiling of the `a × b` rectangle by `n` rectangles is reported. -/
theorem fast_complete (ha : 0 < a) (hb : 0 < b) {x : ℝ} {tl : List Rect}
    (h : IsSimilarTiling x (Rect.main a b) tl) (hcert : FastCertified M P N a b tl.length) :
    FastReported M P N a b tl.length x := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hscaled := h.scale (inv_pos.mpr hbR)
  rw [Rect.scale_main, inv_mul_cancel₀ hbR.ne', inv_mul_eq_div] at hscaled
  have hlen : (tl.map (Rect.scale (b : ℝ)⁻¹)).length = tl.length := List.length_map _
  by_cases hab : a = b
  · have hone : (a : ℝ) / b = 1 := by
      rw [hab]
      exact div_self hbR.ne'
    have hscaled' := hscaled
    rw [hone] at hscaled'
    obtain ⟨path, fresh, hpath, hwide, hsat, -⟩ := completeness_square one_pos hscaled'
    rw [hlen] at hpath
    have hsat' : Satisfies x fresh (initial ((a : ℝ) / b) 1) 0 path := by
      rw [hone]
      exact hsat
    exact ⟨path, hpath, fun _ => hwide, fastSolve_complete P N M hb hpath
      (hcert path hpath fun _ => hwide) ⟨h.one_le, fresh, hsat'⟩⟩
  · obtain ⟨path, fresh, hpath, hsat, -, -⟩ := completeness (div_pos haR hbR) one_pos hscaled
    rw [hlen] at hpath
    exact ⟨path, hpath, fun h => absurd h hab, fastSolve_complete P N M hb hpath
      (hcert path hpath fun h => absurd h hab) ⟨h.one_le, fresh, hsat⟩⟩

/-- **Correctness of the default method.** If the search for `n` tiles is certified, the proportions reported by the default method are exactly the proportions of the tilings of the `a × b` rectangle by `n` rectangles. -/
theorem fast_iff (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hcert : FastCertified M P N a b n) (x : ℝ) :
    FastReported M P N a b n x ↔
      ∃ tl : List Rect, IsSimilarTiling x (Rect.main a b) tl ∧ tl.length = n := by
  constructor
  · exact fast_sound M P N hb
  · rintro ⟨tl, htl, rfl⟩
    exact fast_complete M P N ha hb htl hcert

/-- The default method reports every proportion that the reference method reports. -/
theorem reported_imp_fast (hb : 0 < b) {n : ℕ} {x : ℝ} (h : Reported P a b n x) :
    FastReported M P N a b n x := by
  obtain ⟨path, hpath, hwide, hx⟩ := h
  exact ⟨path, hpath, hwide, solve_subset_fastSolve P N M hb hpath hx⟩

/-- **Agreement of the two methods.** If the search by the reference method is certified, the default method reports the same proportions as the reference method. -/
theorem fast_iff_reported (hb : 0 < b) {n : ℕ} (hcert : Certified P a b n) (x : ℝ) :
    FastReported M P N a b n x ↔ Reported P a b n x := by
  constructor
  · rintro ⟨path, hpath, hwide, hx⟩
    obtain ⟨hs, hc⟩ := hcert path hpath hwide
    rw [fastSolve_eq_solve P N M hb hpath hs hc] at hx
    exact ⟨path, hpath, hwide, hx⟩
  · exact reported_imp_fast M P N hb

end Main

end Fast

end Rectiling
