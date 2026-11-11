-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Staircase

/-!
# Linear forms

Model of `src/form.rs`: linear forms in the unknown lengths, with coefficients polynomial in the tile proportion, divided by a power of the proportion.
The symbolic system emitted by a placement sequence is the system emitted over these forms, and its value at a real proportion and real unknowns is the system emitted over the reals.
-/

open Polynomial

namespace Rectiling

/-- Evaluation of an integer polynomial at a real number. -/
noncomputable def evalAt (x : ℝ) : ℤ[X] →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) x

@[simp]
theorem evalAt_X (x : ℝ) : evalAt x X = x := by
  simp [evalAt]

@[simp]
theorem evalAt_C (x : ℝ) (z : ℤ) : evalAt x (C z) = z := by
  simp [evalAt]

/-- Linear form in the unknown lengths, divided by a power of the tile proportion: coefficient zero is the constant term, coefficient one multiplies the width of the main rectangle, and the remaining coefficients multiply the free tile sides. -/
structure Form where
  /-- Exponent of the power of the proportion in the denominator. -/
  den : ℕ
  /-- Coefficients, by index of unknown. -/
  coeff : ℕ → ℤ[X]

namespace Form

/-- The form consisting of the unknown with the given index alone. -/
noncomputable def unknown (i : ℕ) : Form :=
  ⟨0, fun j => if j = i then 1 else 0⟩

/-- The coefficients over a larger power of the proportion in the denominator. -/
noncomputable def raised (f : Form) (den : ℕ) (j : ℕ) : ℤ[X] :=
  f.coeff j * X ^ (den - f.den)

/-- Sum. -/
noncomputable def add (a b : Form) : Form :=
  ⟨max a.den b.den, fun j => a.raised (max a.den b.den) j + b.raised (max a.den b.den) j⟩

/-- Difference. -/
noncomputable def sub (a b : Form) : Form :=
  ⟨max a.den b.den, fun j => a.raised (max a.den b.den) j - b.raised (max a.den b.den) j⟩

/-- Product with the tile proportion. -/
noncomputable def mulX (a : Form) : Form :=
  if 0 < a.den then ⟨a.den - 1, a.coeff⟩ else ⟨0, fun j => a.coeff j * X⟩

/-- Quotient by the tile proportion. -/
def divX (a : Form) : Form :=
  ⟨a.den + 1, a.coeff⟩

/-- The value of the numerator, for unknowns of index below `m`. -/
noncomputable def num (m : ℕ) (x : ℝ) (u : ℕ → ℝ) (f : Form) : ℝ :=
  ∑ j ∈ Finset.range m, evalAt x (f.coeff j) * u j

/-- The value of the form, for unknowns of index below `m`. -/
noncomputable def value (m : ℕ) (x : ℝ) (u : ℕ → ℝ) (f : Form) : ℝ :=
  f.num m x u / x ^ f.den

variable {m : ℕ} {x : ℝ} {u : ℕ → ℝ}

theorem num_raised (f : Form) (d : ℕ) :
    ∑ j ∈ Finset.range m, evalAt x (f.raised d j) * u j = f.num m x u * x ^ (d - f.den) := by
  rw [num, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [raised, map_mul, map_pow, evalAt_X]
  ring

theorem raised_div (hx : x ≠ 0) (f : Form) {d : ℕ} (hd : f.den ≤ d) :
    f.num m x u * x ^ (d - f.den) / x ^ d = f.value m x u := by
  have hpow : x ^ d = x ^ f.den * x ^ (d - f.den) := by
    rw [← pow_add, Nat.add_sub_cancel' hd]
  rw [value, hpow]
  exact mul_div_mul_right _ _ (pow_ne_zero _ hx)

theorem value_add (hx : x ≠ 0) (a b : Form) :
    (a.add b).value m x u = a.value m x u + b.value m x u := by
  rw [← raised_div hx a (le_max_left a.den b.den), ← raised_div hx b (le_max_right a.den b.den),
    ← add_div, ← num_raised, ← num_raised, ← Finset.sum_add_distrib]
  simp only [value, num, add, map_add, add_mul]

theorem value_sub (hx : x ≠ 0) (a b : Form) :
    (a.sub b).value m x u = a.value m x u - b.value m x u := by
  rw [← raised_div hx a (le_max_left a.den b.den), ← raised_div hx b (le_max_right a.den b.den),
    ← sub_div, ← num_raised, ← num_raised, ← Finset.sum_sub_distrib]
  simp only [value, num, sub, map_sub, sub_mul]

theorem value_mulX (hx : x ≠ 0) (a : Form) : a.mulX.value m x u = x * a.value m x u := by
  unfold mulX
  split
  · rename_i h
    have hpow : x ^ a.den = x ^ (a.den - 1) * x := by
      rw [← pow_succ, Nat.sub_add_cancel h]
    simp only [value, num, hpow]
    field_simp
  · rename_i h
    have h0 : a.den = 0 := by omega
    simp only [value, num, h0, pow_zero, div_one, map_mul, evalAt_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem value_divX (hx : x ≠ 0) (a : Form) : a.divX.value m x u = a.value m x u / x := by
  simp only [value, num, divX, pow_succ]
  field_simp

theorem value_unknown (i : ℕ) :
    (unknown i).value m x u = if i < m then u i else 0 := by
  simp [value, num, unknown, apply_ite (evalAt x), ite_mul, Finset.sum_ite_eq']

end Form

/-- The arithmetic of linear forms. -/
noncomputable def formAlgebra : Algebra Form :=
  ⟨Form.add, Form.sub, Form.mulX, Form.divX⟩

/-- Evaluation at a non-zero proportion is compatible with the arithmetic of forms and of real lengths. -/
theorem formAlgebra_isHom {x : ℝ} (hx : x ≠ 0) (m : ℕ) (u : ℕ → ℝ) :
    formAlgebra.IsHom (realAlgebra x) (Form.value m x u) :=
  ⟨Form.value_add hx, Form.value_sub hx, Form.value_mulX hx, Form.value_divX hx⟩

/-- The symbolic free side of the inside placement of index `j`. -/
noncomputable def symFresh (j : ℕ) : Form :=
  Form.unknown (j + 2)

/-- The symbolic staircase of the empty main rectangle: its width is the unknown of index one and its height is the constant one. -/
noncomputable def symInitial : List (Tier Form) :=
  initial (Form.unknown 1) (Form.unknown 0)

/-- The symbolic equations emitted by a sequence of placements. -/
noncomputable def symEquations (path : List Placement) : List Form :=
  equations formAlgebra symFresh symInitial 0 path

/-- The symbolic positivity constraints emitted by a sequence of placements. -/
noncomputable def symPositives (path : List Placement) : List Form :=
  positives formAlgebra symFresh symInitial 0 path

/-- The constraints emitted over the reals hold exactly when the symbolic constraints hold at the given proportion and unknowns, the constant unknown being one. -/
theorem satisfies_iff_forms {x : ℝ} (hx : x ≠ 0) (path : List Placement) (u : ℕ → ℝ)
    (hu : u 0 = 1) :
    Satisfies x (fun j => u (j + 2)) (initial (u 1) 1) 0 path ↔
      (∀ f ∈ symPositives path, 0 < f.value (finalIndex 0 path + 2) x u) ∧
        ∀ e ∈ symEquations path, e.value (finalIndex 0 path + 2) x u = 0 := by
  have hom := formAlgebra_isHom hx (finalIndex 0 path + 2) u
  have hinit : symInitial.map (Tier.map (Form.value (finalIndex 0 path + 2) x u)) =
      initial (u 1) 1 := by
    simp [symInitial, initial, Tier.map, Form.value_unknown, hu]
  have hcongr := run_congr (realAlgebra x) (f := Form.value (finalIndex 0 path + 2) x u ∘ symFresh)
    (g := fun j => u (j + 2)) path (initial (u 1) 1) 0 (by
      intro j _ hj
      have hlt : j + 2 < finalIndex 0 path + 2 := by omega
      simp only [Function.comp_apply, symFresh, Form.value_unknown, hlt, ite_true])
  have hpos := positives_map hom symFresh symInitial 0 path
  have heq := equations_map hom symFresh symInitial 0 path
  rw [hinit, hcongr.2.1] at hpos
  rw [hinit, hcongr.2.2] at heq
  unfold Satisfies symPositives symEquations
  rw [hpos, heq]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

end Rectiling
