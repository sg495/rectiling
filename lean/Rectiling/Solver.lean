-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Forms

/-!
# The reference method

Model of `solve_in` in `src/exact.rs`, and its algebraic specification: the proportions reported for a complete admissible placement sequence are the real numbers `x ≥ 1` at which the emitted system has a solution satisfying every constraint.

The exact-arithmetic primitives are not modelled.
They enter through the structure `Primitives`, whose fields state what each primitive is assumed to compute.
-/

open Polynomial

namespace Rectiling

/-! ### Cramer's rule under a ring homomorphism -/

section Cramer

variable {n : Type} [Fintype n] [DecidableEq n] {R S : Type} [CommRing R] [CommRing S]

/-- The image of Cramer's solution solves the image of the system, up to the determinant. -/
theorem map_mulVec_cramer (φ : R →+* S) (A : Matrix n n R) (c : n → R) (r : n) :
    ∑ j, φ (A r j) * φ (A.cramer c j) = φ A.det * φ (c r) := by
  have h := congrFun (Matrix.mulVec_cramer A c) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [← map_mul, ← h, map_sum]
  simp only [map_mul]

/-- Every solution of the image of the system is the image of Cramer's solution, up to the determinant. -/
theorem map_cramer_of_solution (φ : R →+* S) (A : Matrix n n R) (c : n → R) (v : n → S)
    (h : ∀ r, ∑ j, φ (A r j) * v j = φ (c r)) (i : n) : φ A.det * v i = φ (A.cramer c i) := by
  have hadj : ∀ j, ∑ r, φ (A.adjugate i r) * φ (A r j) = if i = j then φ A.det else 0 := by
    intro j
    have h1 := congrFun (congrFun (Matrix.adjugate_mul A) i) j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero] at h1
    simp only [← map_mul, ← map_sum, h1]
    split <;> simp
  rw [Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  calc φ A.det * v i = ∑ j, (if i = j then φ A.det else 0) * v j := by simp
    _ = ∑ j, (∑ r, φ (A.adjugate i r) * φ (A r j)) * v j := by simp only [hadj]
    _ = ∑ r, φ (A.adjugate i r) * ∑ j, φ (A r j) * v j := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    _ = ∑ r, φ (A.adjugate i r) * φ (c r) := by simp only [h]

end Cramer

/-! ### The assumed primitives -/

/-- The exact-arithmetic primitives used by the reference method, with the specifications they are assumed to meet. -/
structure Primitives where
  /-- Fraction-free elimination with back-substitution: for a square system, either a failure, or a denominator and one numerator for each unknown. -/
  eliminate : {m : ℕ} → Matrix (Fin m) (Fin m) ℤ[X] → (Fin m → ℤ[X]) →
    Option (ℤ[X] × (Fin m → ℤ[X]))
  /-- On success, the denominator is the determinant and the numerators are Cramer's, up to a common factor. -/
  eliminate_some : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ[X]) (c : Fin m → ℤ[X]) (D : ℤ[X])
    (sol : Fin m → ℤ[X]), eliminate A c = some (D, sol) →
    ∃ ε : ℤ[X], D = ε * A.det ∧ ∀ i, sol i = ε * A.cramer c i
  /-- Real-root isolation: the real roots not smaller than one. -/
  roots : ℤ[X] → Finset ℝ
  /-- The roots reported for a non-zero polynomial are exactly its real roots not smaller than one. -/
  mem_roots : ∀ p : ℤ[X], p ≠ 0 → ∀ x : ℝ, x ∈ roots p ↔ 1 ≤ x ∧ evalAt x p = 0
  /-- Sign determination: the sign of a polynomial at an isolated root. -/
  sign : ℝ → ℤ[X] → SignType
  /-- The sign reported at an isolated root is the sign of the value of the polynomial there. -/
  sign_eq : ∀ (p : ℤ[X]) (x : ℝ), x ∈ roots p → ∀ q : ℤ[X],
    sign x q = SignType.sign (evalAt x q)

open Classical in
/-- Primitives that meet the specifications, which are therefore consistent. -/
noncomputable def Primitives.ideal : Primitives where
  eliminate A c := some (A.det, A.cramer c)
  eliminate_some A c D sol h := by
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨1, by simp, by simp⟩
  roots p := ((p.map (Int.castRingHom ℝ)).roots.toFinset).filter fun x => 1 ≤ x
  mem_roots p hp x := by
    have hmap : p.map (Int.castRingHom ℝ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (RingHom.injective_int (Int.castRingHom ℝ))).mpr hp
    simp only [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hmap,
      Polynomial.IsRoot.def, Polynomial.eval_map, evalAt, Polynomial.coe_eval₂RingHom]
    exact and_comm
  sign x q := SignType.sign (evalAt x q)
  sign_eq _ _ _ _ := rfl

/-! ### The linear system -/

noncomputable instance : Inhabited Form :=
  ⟨⟨0, fun _ => 0⟩⟩

/-- The matrix of the system: one row for each equation, one column for each free side, and a last column for the width of the main rectangle. -/
noncomputable def systemMatrix (k : ℕ) (eqs : List Form) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ[X] :=
  fun r j => if (j : ℕ) < k then (eqs.getD r default).coeff (2 + j) else (eqs.getD r default).coeff 1

/-- The right-hand side of the system. -/
noncomputable def systemRhs (k : ℕ) (eqs : List Form) : Fin (k + 1) → ℤ[X] :=
  fun r => -(eqs.getD r default).coeff 0

/-- The numerator of a form at the solution of the system, over the common denominator. -/
noncomputable def numerator (k : ℕ) (D : ℤ[X]) (sol : Fin (k + 1) → ℤ[X]) (f : Form) : ℤ[X] :=
  f.coeff 0 * D + f.coeff 1 * sol (Fin.last k) + ∑ j : Fin k, f.coeff (2 + j) * sol j.castSucc

/-- The unknowns of the system, read from an assignment of all unknowns. -/
noncomputable def unknowns (k : ℕ) (u : ℕ → ℝ) : Fin (k + 1) → ℝ :=
  fun j => if (j : ℕ) < k then u (2 + j) else u 1

theorem num_eq (k : ℕ) (x : ℝ) (u : ℕ → ℝ) (f : Form) :
    f.num (k + 2) x u = evalAt x (f.coeff 0) * u 0 + evalAt x (f.coeff 1) * u 1 +
      ∑ j : Fin k, evalAt x (f.coeff (2 + j)) * u (2 + j) := by
  rw [Form.num, Finset.sum_range_succ', Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun j => evalAt x (f.coeff (2 + j)) * u (2 + j)) k]
  have : ∀ j : ℕ, j + 1 + 1 = 2 + j := fun j => by omega
  simp only [this, zero_add]
  ring

theorem row_sum (k : ℕ) (x : ℝ) (eqs : List Form) (r : Fin (k + 1)) (u : ℕ → ℝ) :
    ∑ j, evalAt x (systemMatrix k eqs r j) * unknowns k u j =
      evalAt x ((eqs.getD r default).coeff 1) * u 1 +
        ∑ j : Fin k, evalAt x ((eqs.getD r default).coeff (2 + j)) * u (2 + j) := by
  rw [Fin.sum_univ_castSucc]
  simp [systemMatrix, unknowns, add_comm]

/-- The rows of the system hold at an assignment whose constant is one exactly when the numerators of the equations vanish there. -/
theorem rows_iff {k : ℕ} {x : ℝ} {eqs : List Form} (hlen : eqs.length = k + 1) {u : ℕ → ℝ}
    (hu : u 0 = 1) :
    (∀ r, ∑ j, evalAt x (systemMatrix k eqs r j) * unknowns k u j = evalAt x (systemRhs k eqs r)) ↔
      ∀ e ∈ eqs, e.num (k + 2) x u = 0 := by
  have key : ∀ r : Fin (k + 1),
      (∑ j, evalAt x (systemMatrix k eqs r j) * unknowns k u j = evalAt x (systemRhs k eqs r)) ↔
        (eqs.getD r default).num (k + 2) x u = 0 := by
    intro r
    rw [row_sum, num_eq, hu]
    simp only [systemRhs, map_neg, mul_one]
    constructor <;> intro h <;> linarith
  constructor
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have := (key ⟨i, by omega⟩).mp (h ⟨i, by omega⟩)
    simpa [List.getElem?_eq_getElem hi] using this
  · intro h r
    refine (key r).mpr (h _ ?_)
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _

/-- The value of a numerator at a solution of the system is the value of the denominator times the value of the numerator of the form. -/
theorem evalAt_numerator {k : ℕ} {x : ℝ} {D : ℤ[X]} {sol : Fin (k + 1) → ℤ[X]} {u : ℕ → ℝ}
    (hu : u 0 = 1) (h : ∀ i, evalAt x D * unknowns k u i = evalAt x (sol i)) (f : Form) :
    evalAt x (numerator k D sol f) = evalAt x D * f.num (k + 2) x u := by
  have hlast : evalAt x (sol (Fin.last k)) = evalAt x D * u 1 := by
    rw [← h]
    simp [unknowns]
  have hcast : ∀ j : Fin k, evalAt x (sol j.castSucc) = evalAt x D * u (2 + j) := by
    intro j
    rw [← h]
    simp [unknowns]
  rw [num_eq, hu]
  simp only [numerator, map_add, map_mul, map_sum, hlast, hcast, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-! ### A sufficient test for the absence of roots -/

/-- The expansion of the polynomial in `X - 1` has coefficients of one sign and a non-zero constant term. -/
def NoRootTest (p : ℤ[X]) : Prop :=
  ((∀ i, 0 ≤ (p.comp (X + 1)).coeff i) ∨ ∀ i, (p.comp (X + 1)).coeff i ≤ 0) ∧
    (p.comp (X + 1)).coeff 0 ≠ 0

/-- A polynomial that passes the test has no real root not smaller than one. -/
theorem NoRootTest.ne_zero {p : ℤ[X]} (h : NoRootTest p) {x : ℝ} (hx : 1 ≤ x) : evalAt x p ≠ 0 := by
  have hcomp : evalAt (x - 1) (p.comp (X + 1)) = evalAt x p := by
    simp [evalAt, Polynomial.eval₂_comp]
  rw [← hcomp]
  set q := p.comp (X + 1)
  have hy : 0 ≤ x - 1 := by linarith
  have hsum : evalAt (x - 1) q =
      ∑ i ∈ Finset.range q.natDegree, ((q.coeff (i + 1) : ℤ) : ℝ) * (x - 1) ^ (i + 1) +
        ((q.coeff 0 : ℤ) : ℝ) := by
    simp only [evalAt, Polynomial.coe_eval₂RingHom]
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ']
    simp
  rw [hsum]
  obtain ⟨hsign, h0⟩ := h
  rcases hsign with hs | hs
  · have h1 : (0 : ℝ) ≤ ∑ i ∈ Finset.range q.natDegree, ((q.coeff (i + 1) : ℤ) : ℝ) * (x - 1) ^ (i + 1) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast hs (i + 1)) (pow_nonneg hy _)
    have h2 : (0 : ℝ) < ((q.coeff 0 : ℤ) : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (hs 0) (Ne.symm h0)
    linarith
  · have h1 : ∑ i ∈ Finset.range q.natDegree, ((q.coeff (i + 1) : ℤ) : ℝ) * (x - 1) ^ (i + 1) ≤ 0 :=
      Finset.sum_nonpos fun i _ =>
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hs (i + 1)) (pow_nonneg hy _)
    have h2 : ((q.coeff 0 : ℤ) : ℝ) < 0 := by
      exact_mod_cast lt_of_le_of_ne (hs 0) h0
    linarith

/-! ### The method -/

/-- Outcome of the reference method for one placement sequence with orientations. -/
structure Solved where
  /-- The proportions realised by the sequence. -/
  feasible : Finset ℝ
  /-- Number of singular situations met. -/
  singular : ℕ
  /-- Whether the aspect ratio of the main rectangle does not depend on the proportion. -/
  constant : Bool

/-- The proportion equation, for a main rectangle of width `a` and height `b`, given the denominator `D` and the numerator `N` of its aspect ratio. -/
noncomputable def target (a b : ℤ) (D N : ℤ[X]) : ℤ[X] :=
  C b * N - C a * D

open Classical in
/-- The reference method, for a main rectangle of width `a` and height `b`. -/
noncomputable def solve (P : Primitives) (a b : ℤ) (path : List Placement) : Solved :=
  match P.eliminate (systemMatrix (finalIndex 0 path) (symEquations path))
      (systemRhs (finalIndex 0 path) (symEquations path)) with
  | none => ⟨∅, 1, false⟩
  | some (D, sol) =>
    if target a b D (sol (Fin.last _)) = 0 then ⟨∅, 0, true⟩
    else if NoRootTest (target a b D (sol (Fin.last _))) then ⟨∅, 0, false⟩
    else
      ⟨(P.roots (target a b D (sol (Fin.last _)))).filter fun r =>
          P.sign r D ≠ 0 ∧
            ∀ f ∈ symPositives path, P.sign r (numerator _ D sol f) = P.sign r D,
        ((P.roots (target a b D (sol (Fin.last _)))).filter fun r => P.sign r D = 0).card, false⟩

/-! ### The specification -/

/-- A complete admissible sequence emits one more equation than it has inside placements. -/
theorem length_symEquations {n : ℕ} {path : List Placement} (hpath : Complete n path) :
    (symEquations path).length = finalIndex 0 path + 1 := by
  have hunit : Allowed unitAlgebra (fun _ => ()) (initial () ()) 0 path := by
    have aux : ∀ (path : List Placement) (s : List (Tier Unit)) (n k : ℕ),
        CompleteFrom s n path → Allowed unitAlgebra (fun _ => ()) s k path := by
      intro path
      induction path with
      | nil => intro s n k h; exact h
      | cons mv rest ih => intro s n k h; exact ⟨h.1.1, ih _ _ _ h.2⟩
    exact aux path _ n 0 hpath
  have hsym : Allowed formAlgebra symFresh symInitial 0 path :=
    (allowed_map (Algebra.isHom_unit formAlgebra) symFresh symInitial 0 path).mp hunit
  have := length_equations formAlgebra symFresh path symInitial 0 hsym
  simp only [symInitial, initial, List.length_cons, List.length_nil, add_zero] at this
  unfold symEquations symInitial initial
  omega

theorem pos_of_sign_mul_eq {d t : ℝ} (hd : d ≠ 0) (h : SignType.sign (d * t) = SignType.sign d) :
    0 < t := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · rw [sign_neg hneg, sign_eq_neg_one_iff] at h
    by_contra hc
    have := mul_nonneg_of_nonpos_of_nonpos hneg.le (not_lt.mp hc)
    linarith
  · rw [sign_pos hpos, sign_eq_one_iff] at h
    exact (mul_pos_iff_of_pos_left hpos).mp h

/-- Where the denominator does not vanish, the numerators over the denominator solve the system. -/
theorem exists_solution {k : ℕ} {eqs : List Form} (hlen : eqs.length = k + 1) {D ε : ℤ[X]}
    {sol : Fin (k + 1) → ℤ[X]} (hD : D = ε * (systemMatrix k eqs).det)
    (hsol : ∀ i, sol i = ε * (systemMatrix k eqs).cramer (systemRhs k eqs) i) {x : ℝ}
    (hDx : evalAt x D ≠ 0) :
    ∃ u : ℕ → ℝ, u 0 = 1 ∧ u 1 = evalAt x (sol (Fin.last k)) / evalAt x D ∧
      (∀ e ∈ eqs, e.num (k + 2) x u = 0) ∧
      ∀ i, evalAt x D * unknowns k u i = evalAt x (sol i) := by
  let w : ℕ → ℝ := fun i => if h : i < k + 1 then evalAt x (sol ⟨i, h⟩) / evalAt x D else 0
  let u : ℕ → ℝ := fun j => if j = 0 then 1 else if j = 1 then w k else w (j - 2)
  have hu0 : u 0 = 1 := by simp [u]
  have hwk : w k = evalAt x (sol (Fin.last k)) / evalAt x D := by
    simp [w, Fin.last]
  have hu1 : u 1 = evalAt x (sol (Fin.last k)) / evalAt x D := by
    simp [u, hwk]
  have hunk : ∀ i : Fin (k + 1), unknowns k u i = evalAt x (sol i) / evalAt x D := by
    intro i
    unfold unknowns
    split
    · have hlt : (i : ℕ) < k + 1 := i.isLt
      have hw : w i = evalAt x (sol i) / evalAt x D := by
        simp only [w, hlt, ↓reduceDIte]
      have h1 : 2 + (i : ℕ) ≠ 1 := by omega
      simp [u, hw, h1]
    · rename_i hi
      have hik : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hik, hu1]
  have hrows : ∀ r, ∑ j, evalAt x (systemMatrix k eqs r j) * unknowns k u j =
      evalAt x (systemRhs k eqs r) := by
    intro r
    have hcr := map_mulVec_cramer (evalAt x) (systemMatrix k eqs) (systemRhs k eqs) r
    have hDε : evalAt x D = evalAt x ε * evalAt x (systemMatrix k eqs).det := by
      rw [hD, map_mul]
    calc ∑ j, evalAt x (systemMatrix k eqs r j) * unknowns k u j
        = (evalAt x ε * ∑ j, evalAt x (systemMatrix k eqs r j) *
            evalAt x ((systemMatrix k eqs).cramer (systemRhs k eqs) j)) / evalAt x D := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hunk, hsol, map_mul]
          ring
      _ = evalAt x (systemRhs k eqs r) := by
          rw [hcr, ← mul_assoc, ← hDε]
          field_simp
  refine ⟨u, hu0, hu1, (rows_iff hlen hu0).mp hrows, fun i => ?_⟩
  rw [hunk]
  field_simp

/-- **Soundness of the reference method.** Every reported proportion is a real number `x ≥ 1` at which the system emitted for a main rectangle of width `a / b` and height one has a solution satisfying every constraint. -/
theorem solve_sound (P : Primitives) {a b : ℤ} (hb : b ≠ 0) {n : ℕ} {path : List Placement}
    (hpath : Complete n path) {x : ℝ} (hx : x ∈ (solve P a b path).feasible) :
    1 ≤ x ∧ ∃ fresh : ℕ → ℝ, Satisfies x fresh (initial ((a : ℝ) / b) 1) 0 path := by
  have hlen := length_symEquations hpath
  unfold solve at hx
  split at hx
  · simp at hx
  · rename_i D sol helim
    split_ifs at hx with h1 h2
    · simp at hx
    · simp at hx
    · rw [Finset.mem_filter] at hx
      obtain ⟨hroot, hsD, hsf⟩ := hx
      obtain ⟨hx1, htarget⟩ := (P.mem_roots _ h1 x).mp hroot
      obtain ⟨ε, hD, hsol⟩ := P.eliminate_some _ _ _ _ helim
      have hx0 : 0 < x := by linarith
      have hDx : evalAt x D ≠ 0 := by
        rw [P.sign_eq _ x hroot] at hsD
        exact fun h => hsD (sign_eq_zero_iff.mpr h)
      obtain ⟨u, hu0, hu1, heqs, hsolve⟩ := exists_solution hlen hD hsol hDx
      have hu1' : u 1 = (a : ℝ) / b := by
        have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
        simp only [target, map_sub, map_mul, evalAt_C] at htarget
        rw [hu1, div_eq_div_iff hDx hbR]
        linarith
      refine ⟨hx1, fun j => u (j + 2), ?_⟩
      rw [← hu1']
      refine (satisfies_iff_forms hx0.ne' path u hu0).mpr ⟨?_, ?_⟩
      · intro f hf
        have hnum := evalAt_numerator hu0 hsolve f
        have hsign := hsf f hf
        rw [P.sign_eq _ x hroot, P.sign_eq _ x hroot, hnum] at hsign
        exact div_pos (pos_of_sign_mul_eq hDx hsign) (pow_pos hx0 _)
      · intro e he
        rw [Form.value, heqs e he, zero_div]

/-- **Completeness of the reference method.** If no singular situation is met and the aspect ratio depends on the proportion, every real number `x ≥ 1` at which the system emitted for a main rectangle of width `a / b` and height one has a solution satisfying every constraint is reported. -/
theorem solve_complete (P : Primitives) {a b : ℤ} (hb : b ≠ 0) {n : ℕ} {path : List Placement}
    (hpath : Complete n path) (hsing : (solve P a b path).singular = 0)
    (hconst : (solve P a b path).constant = false) {x : ℝ} (hx : 1 ≤ x) {fresh : ℕ → ℝ}
    (hsat : Satisfies x fresh (initial ((a : ℝ) / b) 1) 0 path) :
    x ∈ (solve P a b path).feasible := by
  have hlen := length_symEquations hpath
  have hx0 : 0 < x := by linarith
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  -- the assignment of all unknowns
  let u : ℕ → ℝ := fun j => if j = 0 then 1 else if j = 1 then (a : ℝ) / b else fresh (j - 2)
  have hu0 : u 0 = 1 := by simp [u]
  have hu1 : u 1 = (a : ℝ) / b := by simp [u]
  have hfresh : (fun j => u (j + 2)) = fresh := by
    funext j
    simp [u]
  have hforms := (satisfies_iff_forms hx0.ne' path u hu0).mp (by rw [hfresh, hu1]; exact hsat)
  obtain ⟨hpos, heqs⟩ := hforms
  have hnum0 : ∀ e ∈ symEquations path, e.num (finalIndex 0 path + 2) x u = 0 := by
    intro e he
    have := heqs e he
    rw [Form.value, div_eq_zero_iff] at this
    exact this.resolve_right (pow_ne_zero _ hx0.ne')
  have hnumpos : ∀ f ∈ symPositives path, 0 < f.num (finalIndex 0 path + 2) x u := by
    intro f hf
    have := hpos f hf
    rw [Form.value, div_pos_iff_of_pos_right (pow_pos hx0 _)] at this
    exact this
  have hrows := (rows_iff hlen hu0).mpr hnum0
  rcases heq : P.eliminate (systemMatrix (finalIndex 0 path) (symEquations path))
      (systemRhs (finalIndex 0 path) (symEquations path)) with _ | ⟨D, sol⟩
  · simp [solve, heq] at hsing
  · simp only [solve, heq] at hsing hconst ⊢
    obtain ⟨ε, hD, hsol⟩ := P.eliminate_some _ _ _ _ heq
    have hsolve : ∀ i, evalAt x D * unknowns (finalIndex 0 path) u i = evalAt x (sol i) := by
      intro i
      have := map_cramer_of_solution (evalAt x) _ _ _ hrows i
      rw [hD, hsol, map_mul, map_mul, mul_assoc, this]
    have htarget : evalAt x (target a b D (sol (Fin.last _))) = 0 := by
      simp only [target, map_sub, map_mul, evalAt_C, ← hsolve]
      have : unknowns (finalIndex 0 path) u (Fin.last _) = (a : ℝ) / b := by
        simp [unknowns, hu1]
      rw [this]
      field_simp
      ring
    split_ifs at hsing hconst ⊢ with h1 h2
    · exact absurd htarget (h2.ne_zero hx)
    · simp only at hsing
      have hroot : x ∈ P.roots (target a b D (sol (Fin.last _))) :=
        (P.mem_roots _ h1 x).mpr ⟨hx, htarget⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hsing
      have hsD := hsing hroot
      rw [Finset.mem_filter]
      refine ⟨hroot, hsD, fun f hf => ?_⟩
      rw [P.sign_eq _ x hroot, P.sign_eq _ x hroot, evalAt_numerator hu0 hsolve f, sign_mul,
        sign_pos (hnumpos f hf), mul_one]

/-- **Specification of the reference method.** For a complete admissible placement sequence on which no singular situation is met and the aspect ratio depends on the proportion, the reported proportions are exactly the real numbers `x ≥ 1` at which the system emitted for a main rectangle of width `a / b` and height one has a solution satisfying every constraint. -/
theorem solve_spec (P : Primitives) {a b : ℤ} (hb : b ≠ 0) {n : ℕ} {path : List Placement}
    (hpath : Complete n path) (hsing : (solve P a b path).singular = 0)
    (hconst : (solve P a b path).constant = false) (x : ℝ) :
    x ∈ (solve P a b path).feasible ↔
      1 ≤ x ∧ ∃ fresh : ℕ → ℝ, Satisfies x fresh (initial ((a : ℝ) / b) 1) 0 path :=
  ⟨solve_sound P hb hpath, fun ⟨hx, _, hsat⟩ => solve_complete P hb hpath hsing hconst hx hsat⟩

end Rectiling
