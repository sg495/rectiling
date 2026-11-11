-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Reduced
import Rectiling.Solver

/-!
# The certified numerical check

Model of `Engine::check` and `Engine::degenerate` in `src/fast.rs`, over Laurent polynomials with integer coefficients, and the correctness of its verdicts.

Interval arithmetic, the enclosure of polynomial values and of roots, the test of divisibility by a minimal polynomial, and the extraction of the coefficients of a Laurent polynomial are not modelled.
They enter through the structure `Numerics`, whose fields state what each is assumed to compute.
-/

open Polynomial LaurentPolynomial

namespace Rectiling

namespace Fast

/-- The coefficients of the forms of the default method: Laurent polynomials in the proportion, with integer coefficients. -/
abbrev Coeff := LaurentPolynomial ℤ

/-- The proportion, as a unit of the ring of coefficients. -/
noncomputable def propX : Coeffˣ :=
  (LaurentPolynomial.isUnit_T (R := ℤ) 1).unit

/-- Evaluation of a Laurent polynomial at a non-zero real number. -/
noncomputable def evalL (x : ℝˣ) : Coeff →+* ℝ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℝ) x

@[simp]
theorem evalL_propX (x : ℝˣ) : evalL x propX = x := by
  simp [evalL, propX, LaurentPolynomial.eval₂_T]

theorem evalL_toLaurent (x : ℝˣ) (p : ℤ[X]) : evalL x (toLaurent p) = evalAt x p := by
  simp [evalL, LaurentPolynomial.eval₂_toLaurent, evalAt]

theorem evalL_T_ne_zero (x : ℝˣ) (e : ℤ) : evalL x (T e) ≠ 0 := by
  rw [evalL, LaurentPolynomial.eval₂_T]
  exact (x ^ e).ne_zero

/-! ### The assumed numerical primitives -/

/-- The numerical primitives used by the default method, with the specifications they are assumed to meet. -/
structure Numerics where
  /-- Intervals. -/
  Iv : Type
  /-- The interval encloses the real number. -/
  mem : ℝ → Iv → Prop
  /-- The interval of a single integer. -/
  ofInt : ℤ → Iv
  /-- Sum. -/
  add : Iv → Iv → Iv
  /-- Difference. -/
  sub : Iv → Iv → Iv
  /-- Product. -/
  mul : Iv → Iv → Iv
  /-- Quotient. -/
  div : Iv → Iv → Iv
  /-- Negation. -/
  neg : Iv → Iv
  /-- Whether the interval is not certainly away from zero. -/
  straddles : Iv → Bool
  /-- Whether the interval is certainly not positive. -/
  nonpos : Iv → Bool
  /-- Whether the interval is certainly positive. -/
  pos : Iv → Bool
  /-- Enclosure of the value of a Laurent polynomial over an interval, if it can be computed. -/
  eval : Coeff → Iv → Option Iv
  /-- The interval stored with a root. -/
  rootIv : ℝ → Iv
  /-- The minimal polynomial stored with a root, if it is available. -/
  minPoly : ℝ → Option ℤ[X]
  /-- The test of divisibility of a polynomial by a minimal polynomial. -/
  divides : ℤ[X] → ℤ[X] → Bool
  /-- The normalised coefficients of a proportion polynomial. -/
  key : Coeff → ℤ[X]
  /-- The coefficients of a Laurent polynomial, from the lowest. -/
  coeffs : Coeff → ℤ[X]
  /-- An integer is enclosed by its interval. -/
  mem_ofInt : ∀ z : ℤ, mem z (ofInt z)
  /-- The sum of intervals encloses the sums. -/
  mem_add : ∀ {a b : ℝ} {A B : Iv}, mem a A → mem b B → mem (a + b) (add A B)
  /-- The difference of intervals encloses the differences. -/
  mem_sub : ∀ {a b : ℝ} {A B : Iv}, mem a A → mem b B → mem (a - b) (sub A B)
  /-- The product of intervals encloses the products. -/
  mem_mul : ∀ {a b : ℝ} {A B : Iv}, mem a A → mem b B → mem (a * b) (mul A B)
  /-- The quotient of intervals encloses the quotients, for a divisor certainly away from zero. -/
  mem_div : ∀ {a b : ℝ} {A B : Iv}, mem a A → mem b B → straddles B = false →
    mem (a / b) (div A B)
  /-- The negation of an interval encloses the negations. -/
  mem_neg : ∀ {a : ℝ} {A : Iv}, mem a A → mem (-a) (neg A)
  /-- An interval certainly away from zero does not enclose zero. -/
  ne_zero : ∀ {b : ℝ} {B : Iv}, mem b B → straddles B = false → b ≠ 0
  /-- An interval certainly not positive encloses no positive number. -/
  nonpos_le : ∀ {a : ℝ} {A : Iv}, mem a A → nonpos A = true → a ≤ 0
  /-- An interval certainly positive encloses positive numbers only. -/
  pos_lt : ∀ {a : ℝ} {A : Iv}, mem a A → pos A = true → 0 < a
  /-- The enclosure of a polynomial over an interval certainly away from zero encloses its values at the positive numbers of the interval. -/
  mem_eval : ∀ (x : ℝˣ) {Xi : Iv} {p : Coeff} {V : Iv}, 0 < (x : ℝ) → mem x Xi →
    straddles Xi = false → eval p Xi = some V → mem (evalL x p) V
  /-- The interval stored with a root not smaller than one of a non-zero integer polynomial encloses the root and is certainly away from zero. -/
  mem_rootIv : ∀ (p : ℤ[X]) (r : ℝ), p ≠ 0 → 1 ≤ r → evalAt r p = 0 →
    mem r (rootIv r) ∧ straddles (rootIv r) = false
  /-- The minimal polynomial stored with a root vanishes at the root. -/
  minPoly_root : ∀ {r : ℝ} {f : ℤ[X]}, minPoly r = some f → evalAt r f = 0
  /-- A positive test of divisibility is correct. -/
  divides_dvd : ∀ {f q : ℤ[X]}, divides f q = true → f ∣ q
  /-- The normalised coefficients are those of the Laurent polynomial, up to a sign and a power of the proportion. -/
  key_spec : ∀ c : Coeff, ∃ (e : ℤ) (s : ℤˣ), toLaurent (key c) = ((s : ℤ) : Coeff) * T e * c
  /-- The coefficients are those of the Laurent polynomial, up to a power of the proportion. -/
  coeffs_spec : ∀ c : Coeff, ∃ e : ℤ, toLaurent (coeffs c) = T e * c

namespace Numerics

variable (N : Numerics)

theorem key_eval (c : Coeff) (x : ℝˣ) : evalAt x (N.key c) = 0 ↔ evalL x c = 0 := by
  obtain ⟨e, s, h⟩ := N.key_spec c
  have h1 := congrArg (evalL x) h
  rw [evalL_toLaurent, map_mul, map_mul, map_intCast] at h1
  rw [h1]
  have hs : ((s : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp
  simp [hs, evalL_T_ne_zero]

theorem key_ne_zero {c : Coeff} (hc : c ≠ 0) : N.key c ≠ 0 := by
  obtain ⟨e, s, h⟩ := N.key_spec c
  intro h0
  rw [h0, map_zero] at h
  have hs : ((s : ℤ) : Coeff) ≠ 0 := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp
  have hT : (T e : Coeff) ≠ 0 := (LaurentPolynomial.isUnit_T e).ne_zero
  exact hc ((mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero hs hT))

theorem coeffs_eval {c : Coeff} {x : ℝˣ} (h : evalAt x (N.coeffs c) = 0) : evalL x c = 0 := by
  obtain ⟨e, h'⟩ := N.coeffs_spec c
  have h1 := congrArg (evalL x) h'
  rw [evalL_toLaurent, map_mul, h] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left (evalL_T_ne_zero x e)

/-- The arithmetic of intervals, for the interval of the proportion. -/
def ivAlgebra (xi : N.Iv) : Algebra N.Iv :=
  ⟨N.add, N.sub, fun A => N.mul A xi, fun A => N.div A xi⟩

/-- A real number with an interval that encloses it. -/
def Encl : Type :=
  { p : ℝ × N.Iv // N.mem p.1 p.2 }

/-- The arithmetic of real numbers with enclosing intervals. -/
noncomputable def enclAlgebra {x : ℝ} {xi : N.Iv} (hx : N.mem x xi)
    (hs : N.straddles xi = false) : Algebra N.Encl :=
  ⟨fun p q => ⟨(p.1.1 + q.1.1, N.add p.1.2 q.1.2), N.mem_add p.2 q.2⟩,
    fun p q => ⟨(p.1.1 - q.1.1, N.sub p.1.2 q.1.2), N.mem_sub p.2 q.2⟩,
    fun p => ⟨(x * p.1.1, N.mul p.1.2 xi), by
      have := N.mem_mul p.2 hx
      rwa [mul_comm] at this⟩,
    fun p => ⟨(p.1.1 / x, N.div p.1.2 xi), N.mem_div p.2 hx hs⟩⟩

/-- The positivity constraints replayed on intervals enclose those over the reals, if the intervals of the free sides enclose the free sides. -/
theorem encl_positives {x : ℝ} {xi : N.Iv} (hx : N.mem x xi) (hs : N.straddles xi = false)
    (a b : ℤ) (path : List Placement) {v : ℕ → ℝ} {vals : ℕ → N.Iv}
    (hv : ∀ j, N.mem (v j) (vals j)) :
    ∃ ps : List N.Encl,
      positives (realAlgebra x) (fun j => v (j + 1)) (initial (a : ℝ) (b : ℝ)) 0 path =
        ps.map (fun p => p.1.1) ∧
      positives (N.ivAlgebra xi) (fun j => vals (j + 1)) (initial (N.ofInt a) (N.ofInt b)) 0
        path = ps.map (fun p => p.1.2) := by
  have hfst : (N.enclAlgebra hx hs).IsHom (realAlgebra x) (fun p => p.1.1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hsnd : (N.enclAlgebra hx hs).IsHom (N.ivAlgebra xi) (fun p => p.1.2) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  let fresh : ℕ → N.Encl := fun j => ⟨(v (j + 1), vals (j + 1)), hv (j + 1)⟩
  let init : List (Tier N.Encl) :=
    initial ⟨((a : ℝ), N.ofInt a), N.mem_ofInt a⟩ ⟨((b : ℝ), N.ofInt b), N.mem_ofInt b⟩
  exact ⟨positives (N.enclAlgebra hx hs) fresh init 0 path,
    positives_map hfst fresh init 0 path, positives_map hsnd fresh init 0 path⟩

end Numerics

/-! ### Back-substitution on intervals -/

section Check

variable (N : Numerics)

open Classical in
/-- The sum of the terms of an equation other than that of its eliminated unknown, over the unknowns of index below the bound, on intervals. -/
noncomputable def rowSum (xi : N.Iv) (e : Elim Coeff) (vals : ℕ → N.Iv) : ℕ → Option N.Iv
  | 0 => some (N.ofInt 0)
  | j + 1 =>
    match rowSum xi e vals j with
    | none => none
    | some sum =>
      if j ≠ e.2.1 ∧ e.1 j ≠ 0 then
        (N.eval (e.1 j) xi).map fun c => N.add sum (N.mul c (vals j))
      else some sum

/-- Back-substitution through the recorded equations in reverse order, on intervals; it fails if a coefficient cannot be enclosed or a pivot is not certainly away from zero. -/
noncomputable def backIv (xi : N.Iv) (bound : ℕ) : List (Elim Coeff) → Option (ℕ → N.Iv)
  | [] => some fun j => if j = 0 then N.ofInt 1 else N.ofInt 0
  | e :: rest =>
    match backIv xi bound rest with
    | none => none
    | some vals =>
      match rowSum N xi e vals bound with
      | none => none
      | some sum =>
        match N.eval (e.1 e.2.1) xi with
        | none => none
        | some lead =>
          if N.straddles lead then none
          else some (Function.update vals e.2.1 (N.div (N.neg sum) lead))

variable {N}

theorem rowSum_mem {x : ℝˣ} (hx0 : 0 < (x : ℝ)) {xi : N.Iv} (hx : N.mem x xi)
    (hs : N.straddles xi = false) (e : Elim Coeff) {v : ℕ → ℝ} {vals : ℕ → N.Iv}
    (hv : ∀ j, N.mem (v j) (vals j)) :
    ∀ (bound : ℕ) (S : N.Iv), rowSum N xi e vals bound = some S →
      N.mem (∑ j ∈ Finset.range bound, if j ≠ e.2.1 then evalL x (e.1 j) * v j else 0) S := by
  intro bound
  induction bound with
  | zero =>
    intro S h
    simp only [rowSum, Option.some.injEq] at h
    subst h
    simpa using N.mem_ofInt 0
  | succ j ih =>
    intro S h
    rw [rowSum] at h
    cases hj : rowSum N xi e vals j with
    | none => simp [hj] at h
    | some sum =>
      rw [hj] at h
      simp only at h
      have ih' := ih sum hj
      rw [Finset.sum_range_succ]
      split_ifs at h with hc
      · obtain ⟨c, hc', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [hc.1, ne_eq, not_false_eq_true, ↓reduceIte]
        exact N.mem_add ih' (N.mem_mul (N.mem_eval x hx0 hx hs hc') (hv j))
      · obtain rfl : sum = S := by simpa using h
        have hzero : (if j ≠ e.2.1 then evalL x (e.1 j) * v j else 0) = 0 := by
          by_cases hjm : j = e.2.1
          · simp [hjm]
          · have : e.1 j = 0 := by
              by_contra hne
              exact hc ⟨hjm, hne⟩
            simp [this]
        rw [hzero, add_zero]
        exact ih'

theorem sum_erase_eq_ite (f : ℕ → ℝ) (bound m : ℕ) :
    ∑ j ∈ (Finset.range bound).erase m, f j =
      ∑ j ∈ Finset.range bound, if j ≠ m then f j else 0 := by
  rw [← Finset.sum_filter, Finset.filter_ne']

/-- Back-substitution on intervals, when it succeeds, certifies that no pivot vanishes and encloses back-substitution over the reals. -/
theorem backIv_mem {x : ℝˣ} (hx0 : 0 < (x : ℝ)) {xi : N.Iv} (hx : N.mem x xi)
    (hs : N.straddles xi = false) (bound : ℕ) :
    ∀ (els : List (Elim Coeff)) (vals : ℕ → N.Iv), backIv N xi bound els = some vals →
      (∀ e ∈ els, evalL x (e.1 e.2.1) ≠ 0) ∧
        ∀ j, N.mem (back (evalL x) bound els (fun j => if j = 0 then 1 else 0) j) (vals j) := by
  intro els
  induction els with
  | nil =>
    intro vals h
    simp only [backIv, Option.some.injEq] at h
    subst h
    refine ⟨fun e he => by simp at he, fun j => ?_⟩
    by_cases hj : j = 0
    · subst hj
      simpa [back] using N.mem_ofInt 1
    · simpa [back, hj] using N.mem_ofInt 0
  | cons e rest ih =>
    intro vals h
    rw [backIv] at h
    cases h1 : backIv N xi bound rest with
    | none => simp [h1] at h
    | some vals' =>
      rw [h1] at h
      simp only at h
      cases h2 : rowSum N xi e vals' bound with
      | none => simp [h2] at h
      | some sum =>
        rw [h2] at h
        simp only at h
        cases h3 : N.eval (e.1 e.2.1) xi with
        | none => simp [h3] at h
        | some lead =>
          rw [h3] at h
          simp only at h
          split_ifs at h with hstr
          obtain rfl : Function.update vals' e.2.1 (N.div (N.neg sum) lead) = vals := by
            simpa using h
          have hstr' : N.straddles lead = false := by simpa using hstr
          obtain ⟨hpiv, hmem⟩ := ih vals' h1
          have hlead := N.mem_eval x hx0 hx hs h3
          refine ⟨?_, fun j => ?_⟩
          · intro e' he'
            rcases List.mem_cons.mp he' with rfl | he'
            · exact N.ne_zero hlead hstr'
            · exact hpiv e' he'
          · rw [back_cons]
            by_cases hjm : j = e.2.1
            · subst hjm
              rw [Function.update_self, Function.update_self, sum_erase_eq_ite]
              exact N.mem_div (N.mem_neg (rowSum_mem hx0 hx hs e hmem bound sum h2)) hlead hstr'
            · rw [Function.update_of_ne hjm, Function.update_of_ne hjm]
              exact hmem j

end Check

/-! ### Degenerate tiles -/

section Degenerate

open Classical in
/-- A form carried through a sequence of eliminations with exact divisions, if every division is exact. -/
noncomputable def carryExact {R : Type} [CommRing R] : List (Elim R) → Vec R → Option (Vec R)
  | [], F => some F
  | e :: rest, F => if Divisible e F then carryExact rest (elimForm e F) else none

theorem carryExact_spec {R : Type} [CommRing R] (φ : R →+* ℝ) :
    ∀ (els : List (Elim R)) (F G : Vec R), carryExact els F = some G →
      (∀ e ∈ els, φ e.2.2 ≠ 0) → mapVec φ G = carry φ els (mapVec φ F) := by
  intro els
  induction els with
  | nil =>
    intro F G h _
    simp only [carryExact, Option.some.injEq] at h
    rw [h]
    rfl
  | cons e rest ih =>
    intro F G h hπ
    rw [carryExact] at h
    split_ifs at h with hdiv
    rw [ih _ _ h fun e' he' => hπ e' (by simp [he']), mapVec_elimForm φ (hπ e (by simp)) hdiv]
    rfl

variable (N : Numerics)

open Classical in
/-- Whether one of the given tiles is certified to have size exactly zero at the given root, as in `Engine::degenerate`. -/
noncomputable def degenerate (steps : List (Step Coeff)) (r : ℝ) : List ℕ → Bool
  | [] => false
  | q :: rest =>
    match steps[q]? with
    | none => false
    | some s =>
      match carryExact (elims (steps.drop q)) s.size with
      | none => false
      | some F =>
        if ∃ j, 0 < j ∧ F j ≠ 0 then false
        else if F 0 = 0 then true
        else
          match N.minPoly r with
          | none => false
          | some f => if N.divides f (N.coeffs (F 0)) then true else degenerate steps r rest

variable {N}

/-- A positive answer exhibits a tile whose size, carried through the later eliminations, is a multiple of the scale that vanishes at the root. -/
theorem degenerate_spec (steps : List (Step Coeff)) (x : ℝˣ) :
    ∀ qs : List ℕ, degenerate N steps x qs = true →
      ∃ (q : ℕ) (s : Step Coeff) (F : Vec Coeff), steps[q]? = some s ∧
        carryExact (elims (steps.drop q)) s.size = some F ∧ (∀ j, 0 < j → F j = 0) ∧
        evalL x (F 0) = 0 := by
  intro qs
  induction qs with
  | nil => intro h; simp [degenerate] at h
  | cons q rest ih =>
    intro h
    rw [degenerate] at h
    cases hs : steps[q]? with
    | none => simp [hs] at h
    | some s =>
      rw [hs] at h
      simp only at h
      cases hF : carryExact (elims (steps.drop q)) s.size with
      | none => simp [hF] at h
      | some F =>
        rw [hF] at h
        simp only at h
        split_ifs at h with h1 h2
        · have hz : ∀ j, 0 < j → F j = 0 := by
            intro j hj
            by_contra hne
            exact h1 ⟨j, hj, hne⟩
          exact ⟨q, s, F, hs, hF, hz, by rw [h2, map_zero]⟩
        · have hz : ∀ j, 0 < j → F j = 0 := by
            intro j hj
            by_contra hne
            exact h1 ⟨j, hj, hne⟩
          cases hmp : N.minPoly x with
          | none => simp [hmp] at h
          | some f =>
            rw [hmp] at h
            simp only at h
            split_ifs at h with hd
            · obtain ⟨g, hg⟩ := N.divides_dvd hd
              refine ⟨q, s, F, hs, hF, hz, N.coeffs_eval ?_⟩
              rw [hg, map_mul, N.minPoly_root hmp, zero_mul]
            · exact ih h

end Degenerate

/-! ### The check -/

/-- Verdict of the numerical check of a root. -/
inductive Verdict
  | accept
  | reject
  | unsure
  deriving DecidableEq

section Verdicts

variable (N : Numerics)

/-- The numerical check of a root at the end of a path, as in `Engine::check`. -/
noncomputable def check (a b : ℤ) (path : List Placement) (steps : List (Step Coeff)) (r : ℝ) :
    Verdict :=
  match backIv N (N.rootIv r) (finalIndex 0 path + 1) (elims steps) with
  | none => .unsure
  | some vals =>
    let ps := positives (N.ivAlgebra (N.rootIv r)) (fun j => vals (j + 1))
      (initial (N.ofInt a) (N.ofInt b)) 0 path
    if ps.any N.nonpos then .reject
    else if ps.all N.pos then .accept
    else if degenerate N steps r
        ((List.range ps.length).filter fun q => !(N.pos (ps.getD q (N.ofInt 0)))) then .reject
    else .unsure

variable {N}

theorem dot_scale_only {N' : ℕ} (hN : 0 < N') {G : Vec ℝ} (hG : ∀ j, 0 < j → G j = 0)
    (v : ℕ → ℝ) : dot N' G v = G 0 * v 0 := by
  unfold dot
  rw [Finset.sum_eq_single 0]
  · intro j _ hj
    rw [hG j (Nat.pos_of_ne_zero hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr hN) h

variable {a b : ℤ} {n : ℕ} {path : List Placement} {steps : List (Step Coeff)} {E : Vec Coeff}

/-- **An accepted root is a solution.** If the check accepts a root of the scale coefficient of a final equation that involves the scale only, the constraints over the reals hold for a main rectangle of sides `a` and `b`. -/
theorem check_accept (hpath : Complete n path) (hrun : Run propX (Stage.init a b) path steps E)
    {x : ℝˣ} (hx0 : 0 < (x : ℝ)) (hx : N.mem x (N.rootIv x))
    (hs : N.straddles (N.rootIv x) = false) (hE : ∀ j, 0 < j → E j = 0)
    (hroot : evalL x (E 0) = 0) (hc : check N a b path steps x = .accept) :
    ∃ v : ℕ → ℝ, v 0 = 1 ∧
      Satisfies x (fun j => v (j + 1)) (initial (a : ℝ) (b : ℝ)) 0 path := by
  unfold check at hc
  cases hb : backIv N (N.rootIv x) (finalIndex 0 path + 1) (elims steps) with
  | none => simp [hb] at hc
  | some vals =>
    rw [hb] at hc
    simp only at hc
    obtain ⟨hpiv, hmem'⟩ := backIv_mem hx0 hx hs _ _ vals hb
    have hmem : ∀ j, N.mem (solutionOf (evalL x) path steps j) (vals j) := hmem'
    obtain ⟨hv0, hfinal, -, -⟩ := hrun.solution (evalL x) hpath hpiv
    obtain ⟨ps, hreal, hiv⟩ := N.encl_positives hx hs a b path hmem
    rw [hiv] at hc
    split_ifs at hc with h1 h2
    refine ⟨solutionOf (evalL x) path steps, hv0, ?_⟩
    have hsat := satisfies_iff_hom (evalL x) propX a b path _ hv0
    rw [evalL_propX] at hsat
    have hposhom := positives_hom (evalL x) propX a b path _ hv0
    rw [evalL_propX] at hposhom
    refine hsat.mpr ⟨?_, (hfinal fun j hj => by rw [hE j hj, map_zero]).mpr hroot⟩
    intro p hp
    have hmemp : val (evalL x) (finalIndex 0 path + 1) (solutionOf (evalL x) path steps) p ∈
        ps.map (fun p => p.1.1) := by
      rw [← hreal, hposhom]
      exact List.mem_map_of_mem hp
    obtain ⟨p', hp', hval⟩ := List.mem_map.mp hmemp
    rw [← hval]
    refine N.pos_lt p'.2 ?_
    rw [List.all_eq_true] at h2
    exact h2 _ (List.mem_map_of_mem hp')

/-- **A rejected root is not a solution.** If the check rejects a root, the constraints over the reals fail there for a main rectangle of sides `a` and `b`, whatever the free sides. -/
theorem check_reject (hpath : Complete n path) (hrun : Run propX (Stage.init a b) path steps E)
    {x : ℝˣ} (hx0 : 0 < (x : ℝ)) (hx : N.mem x (N.rootIv x))
    (hs : N.straddles (N.rootIv x) = false) (hc : check N a b path steps x = .reject)
    (w : ℕ → ℝ) (hw0 : w 0 = 1) :
    ¬ Satisfies x (fun j => w (j + 1)) (initial (a : ℝ) (b : ℝ)) 0 path := by
  intro hsatw
  unfold check at hc
  cases hb : backIv N (N.rootIv x) (finalIndex 0 path + 1) (elims steps) with
  | none => simp [hb] at hc
  | some vals =>
    rw [hb] at hc
    simp only at hc
    obtain ⟨hpiv, hmem'⟩ := backIv_mem hx0 hx hs _ _ vals hb
    have hmem : ∀ j, N.mem (solutionOf (evalL x) path steps j) (vals j) := hmem'
    obtain ⟨hv0, -, huniq, πf, hπf, hsizes⟩ := hrun.solution (evalL x) hpath hpiv
    obtain ⟨ps, hreal, hiv⟩ := N.encl_positives hx hs a b path hmem
    rw [hiv] at hc
    have hsat := satisfies_iff_hom (evalL x) propX a b path w hw0
    rw [evalL_propX] at hsat
    obtain ⟨hwpos, hweq⟩ := hsat.mp hsatw
    have hagree := huniq w hw0 hweq
    have hvpos : ∀ p ∈ homPositives propX a b path,
        0 < val (evalL x) (finalIndex 0 path + 1) (solutionOf (evalL x) path steps) p := by
      intro p hp
      rw [← val_congr (evalL x) _ hagree p]
      exact hwpos p hp
    have hposhom := positives_hom (evalL x) propX a b path _ hv0
    rw [evalL_propX] at hposhom
    have hpsall : ∀ p ∈ ps, 0 < p.1.1 := by
      intro p hp
      have hmemp : p.1.1 ∈ ps.map (fun p => p.1.1) := List.mem_map_of_mem hp
      rw [← hreal, hposhom] at hmemp
      obtain ⟨p', hp', hval⟩ := List.mem_map.mp hmemp
      rw [← hval]
      exact hvpos p' hp'
    split_ifs at hc with h1 h2 h3
    · rw [List.any_eq_true] at h1
      obtain ⟨A, hA, hnp⟩ := h1
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA
      exact absurd (hpsall p hp) (not_lt.mpr (N.nonpos_le p.2 hnp))
    · obtain ⟨q, s, F, hsq, hF, hz, hzero⟩ := degenerate_spec steps x _ h3
      obtain ⟨p, hp, hdot⟩ := hsizes q s hsq
      have hprev := hrun.prev_ne_zero (evalL x) hpiv
      have hcar := carryExact_spec (evalL x) _ _ _ hF fun e he =>
        hprev e (by
          rw [← List.take_append_drop q steps, elims_append]
          exact List.mem_append_right _ he)
      rw [← hcar, dot_scale_only (Nat.succ_pos _)
        (fun j hj => by simp only [mapVec]; rw [hz j hj, map_zero])] at hdot
      simp only [mapVec] at hdot
      rw [hzero, zero_mul] at hdot
      have hpz := (mul_eq_zero.mp hdot.symm).resolve_left hπf
      exact absurd (hvpos p (List.mem_of_getElem? hp)) (by rw [hpz]; exact lt_irrefl 0)

end Verdicts

end Fast

end Rectiling
