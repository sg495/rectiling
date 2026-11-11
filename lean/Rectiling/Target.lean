-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Fast

/-!
# The two proportion polynomials

The proportion polynomial of the default method and that of the reference method differ by a sign, a power of the proportion, and the common factor of the fraction-free elimination of the reference method (`Run.final_eq_target`).

The forms of the reference method, in the constant, the width of the main rectangle and the free sides, become the forms of the homogeneous system when the width is `a` times the scale and the constant is `b` times the scale.
-/

open Polynomial

namespace Rectiling

namespace Fast

/-- The coefficient of an unknown of the homogeneous system in a form of the reference method, before division by the power of the proportion. -/
noncomputable def homCoeff (a b : ℤ) (f : Form) (j : ℕ) : ℤ[X] :=
  if j = 0 then C a * f.coeff 1 + C b * f.coeff 0 else f.coeff (j + 1)

/-- The form of the homogeneous system that corresponds to a form of the reference method. -/
noncomputable def toHom (a b : ℤ) (f : Form) : Vec Coeff :=
  fun j => LaurentPolynomial.T (-(f.den : ℤ)) * toLaurent (homCoeff a b f j)

theorem propX_val : (propX : Coeff) = LaurentPolynomial.T 1 :=
  rfl

theorem propX_inv_val : ((propX⁻¹ : Coeffˣ) : Coeff) = LaurentPolynomial.T (-1) := by
  rw [Units.inv_eq_of_mul_eq_one_right]
  rw [propX_val, ← LaurentPolynomial.T_add]
  simp

theorem T_raise {d D : ℕ} (hd : d ≤ D) (p : ℤ[X]) :
    LaurentPolynomial.T (-(D : ℤ)) * toLaurent (p * X ^ (D - d)) =
      LaurentPolynomial.T (-(d : ℤ)) * toLaurent p := by
  rw [map_mul, Polynomial.toLaurent_X_pow, mul_left_comm, ← LaurentPolynomial.T_add, mul_comm]
  congr 2
  rw [Nat.cast_sub hd]
  ring

theorem toHom_isHom (a b : ℤ) : formAlgebra.IsHom (vecAlgebra propX) (toHom a b) where
  add f g := by
    funext j
    have h : homCoeff a b (f.add g) j =
        homCoeff a b f j * X ^ (max f.den g.den - f.den) +
          homCoeff a b g j * X ^ (max f.den g.den - g.den) := by
      simp only [homCoeff, Form.add, Form.raised]
      split_ifs <;> ring
    simp only [formAlgebra, vecAlgebra, toHom]
    rw [h, map_add, mul_add]
    change LaurentPolynomial.T (-((max f.den g.den : ℕ) : ℤ)) * _ +
      LaurentPolynomial.T (-((max f.den g.den : ℕ) : ℤ)) * _ = _
    rw [T_raise (le_max_left _ _), T_raise (le_max_right _ _)]
  sub f g := by
    funext j
    have h : homCoeff a b (f.sub g) j =
        homCoeff a b f j * X ^ (max f.den g.den - f.den) -
          homCoeff a b g j * X ^ (max f.den g.den - g.den) := by
      simp only [homCoeff, Form.sub, Form.raised]
      split_ifs <;> ring
    simp only [formAlgebra, vecAlgebra, toHom]
    rw [h, map_sub, mul_sub]
    change LaurentPolynomial.T (-((max f.den g.den : ℕ) : ℤ)) * _ -
      LaurentPolynomial.T (-((max f.den g.den : ℕ) : ℤ)) * _ = _
    rw [T_raise (le_max_left _ _), T_raise (le_max_right _ _)]
  mulX f := by
    funext j
    simp only [formAlgebra, vecAlgebra, toHom, propX_val]
    unfold Form.mulX
    split_ifs with h
    · have hc : homCoeff a b ⟨f.den - 1, f.coeff⟩ j = homCoeff a b f j := rfl
      rw [hc, ← mul_assoc, ← LaurentPolynomial.T_add]
      congr 2
      simp only
      rw [Nat.cast_sub h]
      ring
    · have h0 : f.den = 0 := by omega
      have hc : homCoeff a b ⟨0, fun j => f.coeff j * X⟩ j = homCoeff a b f j * X := by
        simp only [homCoeff]
        split_ifs <;> ring
      rw [hc, map_mul, Polynomial.toLaurent_X, h0]
      simp only [Nat.cast_zero, neg_zero, LaurentPolynomial.T_zero, one_mul]
      ring
  divX f := by
    funext j
    simp only [formAlgebra, vecAlgebra, toHom, propX_inv_val]
    have hc : homCoeff a b f.divX j = homCoeff a b f j := rfl
    rw [hc, ← mul_assoc, ← LaurentPolynomial.T_add]
    congr 2
    simp only [Form.divX]
    push_cast
    ring

theorem toHom_default (a b : ℤ) : toHom a b default = 0 := by
  funext j
  simp only [toHom, homCoeff]
  change _ * toLaurent (if j = 0 then C a * 0 + C b * 0 else 0) = 0
  simp

/-- The equations of the homogeneous system are those of the reference method. -/
theorem homEquations_eq (a b : ℤ) (path : List Placement) :
    homEquations propX a b path = (symEquations path).map (toHom a b) := by
  have hfresh : toHom a b ∘ symFresh = trueFresh := by
    funext i j
    simp only [Function.comp_apply, toHom, homCoeff, symFresh, Form.unknown, trueFresh, unitVec]
    by_cases hj : j = 0
    · subst hj
      simp
    · have h1 : (j + 1 = i + 2) ↔ (j = i + 1) := by omega
      simp [hj]
  have hinit : symInitial.map (Tier.map (toHom a b)) = homInitial a b := by
    simp only [symInitial, homInitial, initial, List.map_cons, List.map_nil, Tier.map]
    congr 2
    · funext j
      simp only [toHom, homCoeff, Form.unknown, unitVec]
      by_cases hj : j = 0
      · subst hj
        simp
      · simp [hj]
    · funext j
      simp only [toHom, homCoeff, Form.unknown, unitVec]
      by_cases hj : j = 0
      · subst hj
        simp
      · simp [hj]
  have h := equations_map (toHom_isHom a b) symFresh symInitial 0 path
  rw [hfresh, hinit] at h
  exact h

theorem prod_T {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, (LaurentPolynomial.T (f i) : Coeff) = LaurentPolynomial.T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, LaurentPolynomial.T_add]

open Matrix in
/-- **The two proportion polynomials.** Along a complete path on which the symbolic pass succeeds and the elimination of the reference method succeeds, the proportion polynomial of the default method, multiplied by the common factor of that elimination, is the proportion polynomial `b N - a D` of the reference method, up to a sign and a power of the proportion. -/
theorem Run.final_eq_target (P : Primitives) {a b : ℤ} {n : ℕ} {path : List Placement}
    {steps : List (Step Coeff)} {E : Vec Coeff} (hpath : Complete n path)
    (hrun : Run propX (Stage.init a b) path steps E) {D : ℤ[X]}
    {sol : Fin (finalIndex 0 path + 1) → ℤ[X]}
    (helim : P.eliminate (systemMatrix (finalIndex 0 path) (symEquations path))
      (systemRhs (finalIndex 0 path) (symEquations path)) = some (D, sol)) :
    ∃ (ε : ℤ[X]) (s : ℤˣ) (e : ℤ),
      D = ε * (systemMatrix (finalIndex 0 path) (symEquations path)).det ∧
      toLaurent ε * E 0 = ((s : ℤ) : Coeff) * LaurentPolynomial.T e *
        toLaurent (target a b D (sol (Fin.last _))) := by
  set eqs := symEquations path with heqs
  set M : Matrix (Fin (finalIndex 0 path + 1)) (Fin (finalIndex 0 path + 1)) ℤ[X] :=
    systemMatrix (finalIndex 0 path) eqs with hM
  obtain ⟨ε, hD, hsol⟩ := P.eliminate_some M (systemRhs (finalIndex 0 path) eqs) D sol helim
  -- the column of the scale
  let c0 : Fin (finalIndex 0 path + 1) → ℤ[X] := fun i => (eqs.getD i default).coeff 0
  let col : Fin (finalIndex 0 path + 1) → ℤ[X] := fun i =>
    C a * (eqs.getD i default).coeff 1 + C b * (eqs.getD i default).coeff 0
  let Mt : Matrix (Fin (finalIndex 0 path + 1)) (Fin (finalIndex 0 path + 1)) ℤ[X] :=
    Matrix.updateCol M (Fin.last (finalIndex 0 path)) col
  have hMself : Matrix.updateCol M (Fin.last (finalIndex 0 path)) (fun i => M i (Fin.last (finalIndex 0 path))) = M :=
    Matrix.updateCol_eq_self _ _
  have hMt : Mt.det = C a * M.det + C b * Matrix.det (Matrix.updateCol M (Fin.last (finalIndex 0 path)) c0) := by
    have hcol : col = C a • (fun i => M i (Fin.last (finalIndex 0 path))) + C b • c0 := by
      funext i
      simp [col, c0, M, systemMatrix]
    simp only [Mt]
    rw [hcol, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
      Matrix.det_updateCol_smul, hMself]
  have hrhs : Matrix.det (Matrix.updateCol M (Fin.last (finalIndex 0 path)) (systemRhs (finalIndex 0 path) eqs)) =
      -Matrix.det (Matrix.updateCol M (Fin.last (finalIndex 0 path)) c0) := by
    have : systemRhs (finalIndex 0 path) eqs = (-1 : ℤ[X]) • c0 := by
      funext i
      simp [systemRhs, c0]
    rw [this, Matrix.det_updateCol_smul]
    ring
  have htarget : target a b D (sol (Fin.last (finalIndex 0 path))) = -(ε * Mt.det) := by
    rw [target, hsol, hD, Matrix.cramer_apply, hrhs, hMt]
    ring
  -- the matrix of the homogeneous system
  let d : Fin (finalIndex 0 path + 1) → Coeff := fun i => LaurentPolynomial.T (-((eqs.getD i default).den : ℤ))
  let σ : Equiv.Perm (Fin (finalIndex 0 path + 1)) := (finRotate (finalIndex 0 path + 1)).symm
  have hσ0 : σ 0 = Fin.last (finalIndex 0 path) := by
    rw [Equiv.symm_apply_eq, finRotate_last]
  have hσs : ∀ j : Fin (finalIndex 0 path), σ j.succ = j.castSucc := by
    intro j
    rw [Equiv.symm_apply_eq, finRotate_apply, Fin.coeSucc_eq_succ]
  have hA : (Matrix.of fun i j : Fin (finalIndex 0 path + 1) => (homEquations propX a b path).getD i 0 j) =
      Matrix.diagonal d * ((Polynomial.toLaurent (R := ℤ)).mapMatrix Mt).submatrix id σ := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    rw [homEquations_eq, ← toHom_default a b, List.getD_map]
    simp only [toHom, d]
    congr 2
    refine Fin.cases ?_ (fun j' => ?_) j
    · rw [hσ0]
      simp [Mt, col, homCoeff, eqs]
    · rw [hσs]
      have hne : j'.castSucc ≠ Fin.last (finalIndex 0 path) := (Fin.castSucc_lt_last j').ne
      have h1 : ((j'.succ : Fin (finalIndex 0 path + 1)) : ℕ) ≠ 0 := by simp
      have h2 : (j' : ℕ) + 1 + 1 = 2 + j' := by omega
      simp [Mt, M, systemMatrix, homCoeff, h2, eqs]
  obtain ⟨s, hs⟩ := hrun.final_eq_det hpath
  rw [hA, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute', ← RingHom.map_det,
    prod_T] at hs
  refine ⟨ε, -(s * Equiv.Perm.sign σ),
    ∑ i : Fin (finalIndex 0 path + 1), -((eqs.getD i default).den : ℤ), hD, ?_⟩
  rw [hs, htarget]
  simp only [map_neg, map_mul, Units.val_neg, Units.val_mul, Int.cast_neg,
    Int.cast_mul]
  ring

end Fast

end Rectiling
