-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Network

/-!
# The polynomial of a network with an orientation vector

For a network and an orientation vector, which makes each edge tall, with resistance `x`, or wide, with resistance `1 / x`, the determinant of the system that states that the impedance is one is a polynomial in `x` with integer coefficients.
It is not zero, its degree is at most the number of edges, and it vanishes at every `x` at which the network has a flow of non-zero value equal to the potential difference between the poles.
-/

namespace Rectiling

namespace Network

open Polynomial

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The matrix, with polynomial entries, of the system that states that the impedance is one when the edges marked `true` have resistance `X` and the others resistance `1 / X`. -/
noncomputable def pairMatrix (N : Network V E) (ε : E → Bool) : Matrix (E ⊕ V) (E ⊕ V) ℤ[X] :=
  N.system (fun e => if ε e then 1 else X) (fun e => if ε e then X else 1) 1

/-- The polynomial of a network with an orientation vector. -/
noncomputable def pairPoly (N : Network V E) (ε : E → Bool) : ℤ[X] :=
  (N.pairMatrix ε).det

/-- The value of the polynomial at a real number is the determinant of the system with real coefficients. -/
theorem aeval_pairPoly (N : Network V E) (ε : E → Bool) (x : ℝ) :
    aeval x (N.pairPoly ε) =
      (N.system (fun e => if ε e then (1 : ℝ) else x) (fun e => if ε e then x else 1) 1).det := by
  have h := RingHom.map_det (aeval x : ℤ[X] →ₐ[ℤ] ℝ).toRingHom (N.pairMatrix ε)
  rw [RingHom.mapMatrix_apply, pairMatrix, system_map] at h
  have h1 : ∀ b : Bool, (aeval x : ℤ[X] →ₐ[ℤ] ℝ).toRingHom (if b then 1 else X) = if b then 1 else x := by
    intro b
    cases b <;> simp
  have h2 : ∀ b : Bool, (aeval x : ℤ[X] →ₐ[ℤ] ℝ).toRingHom (if b then X else 1) = if b then x else 1 := by
    intro b
    cases b <;> simp
  simp only [h1, h2, map_one] at h
  exact h

omit [Fintype V] [Fintype E] in
theorem natDegree_pairMatrix_le (N : Network V E) (ε : E → Bool) (p q : E ⊕ V) :
    (N.pairMatrix ε p q).natDegree ≤ Sum.elim (fun _ => 1) (fun _ => 0) p := by
  rcases p with e | v <;> rcases q with e' | v' <;>
    simp only [pairMatrix, system, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp

/-- The degree of the polynomial is at most the number of edges. -/
theorem natDegree_pairPoly_le (N : Network V E) (ε : E → Bool) :
    (N.pairPoly ε).natDegree ≤ Fintype.card E := by
  rw [pairPoly, Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine natDegree_mul_le.trans ?_
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℤ[X]).natDegree = 0 := natDegree_intCast _
  rw [h1, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ q, (N.pairMatrix ε (σ q) q).natDegree
      ≤ ∑ q, Sum.elim (fun _ => 1) (fun _ => 0) (σ q) :=
        Finset.sum_le_sum fun q _ => N.natDegree_pairMatrix_le ε (σ q) q
    _ = ∑ p : E ⊕ V, Sum.elim (fun _ => 1) (fun _ => 0) p :=
        Equiv.sum_comp σ (Sum.elim (fun _ => 1) (fun _ => 0))
    _ = Fintype.card E := by simp

/-- The polynomial vanishes at `x` when currents and potentials, with a non-zero potential at the source and potential zero at the sink, satisfy Ohm's law for the resistances `x` and `1 / x`, Kirchhoff's law away from the poles, and have net current at the source equal to its potential. -/
theorem aeval_pairPoly_eq_zero (N : Network V E) {ε : E → Bool} {x : ℝ} {φ : V → ℝ} {i : E → ℝ}
    (hohm : ∀ e, (if ε e then 1 else x) * (φ (N.tail e) - φ (N.head e)) = (if ε e then x else 1) * i e)
    (hk : ∀ v, v ≠ N.sink → v ≠ N.source → N.div i v = 0) (hs : N.div i N.source = φ N.source)
    (ht : φ N.sink = 0) (hne : φ N.source ≠ 0) : aeval x (N.pairPoly ε) = 0 := by
  rw [aeval_pairPoly]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim i φ, fun h => ?_, ?_⟩
  · exact hne (by simpa using congrFun h (.inr N.source))
  · funext p
    rcases p with e | v
    · rw [system_mulVec_inl]
      simpa using sub_eq_zero.mpr (hohm e)
    · rw [system_mulVec_inr]
      by_cases hv : v = N.sink
      · simp [hv, ht]
      · by_cases hs' : v = N.source
        · subst hs'
          simp [hv, hs]
        · simp [hv, hs', hk v hv hs']

/-- The polynomial vanishes at every `x > 0` at which the impedance of the network is one. -/
theorem IsFlow.aeval_pairPoly {N : Network V E} {ε : E → Bool} {x I : ℝ} {φ : V → ℝ} {i : E → ℝ}
    (hst : N.source ≠ N.sink) (hx : 0 < x) (h : N.IsFlow (fun e => if ε e then x else x⁻¹) I φ i)
    (hI : I ≠ 0) (hZ : φ N.source - φ N.sink = I) : aeval x (N.pairPoly ε) = 0 := by
  refine N.aeval_pairPoly_eq_zero (φ := fun v => φ v - φ N.sink) (i := i) (fun e => ?_) (fun v hv hs => ?_)
    ?_ (sub_self _) (by rw [hZ]; exact hI)
  · have := h.ohm e
    cases hε : ε e <;> simp only [hε, Bool.false_eq_true, ite_false, ite_true] at this ⊢
    · rw [one_mul, sub_sub_sub_cancel_right, this, mul_inv_cancel_left₀ hx.ne']
    · rw [one_mul, sub_sub_sub_cancel_right, this]
  · rw [h.kirchhoff]
    simp [hv, hs]
  · rw [h.kirchhoff, hZ]
    simp [hst]

/-- The polynomial of a connected network is not zero. -/
theorem Proper.pairPoly_ne_zero {N : Network V E} (hN : N.Proper) (ε : E → Bool) : N.pairPoly ε ≠ 0 := by
  intro h0
  have h1 : aeval (-1 : ℝ) (N.pairPoly ε) = 0 := by rw [h0, map_zero]
  rw [aeval_pairPoly] at h1
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
  obtain ⟨h1, h2, h3⟩ := N.system_mulVec_eq_zero hu
  have hf : N.IsFlow (fun _ => -1) (1 * u (.inr N.source)) (fun v => u (.inr v)) (fun e => u (.inl e)) := by
    refine ⟨fun e => ?_, N.div_eq_of_ne_sink hN.source_ne_sink h2⟩
    have := h1 e
    cases hε : ε e <;> simp only [hε, Bool.false_eq_true, ite_false, ite_true] at this <;> linarith
  obtain ⟨h4, h5⟩ := hf.trivial_of_neg hN (fun _ => by norm_num) (by
    simp only [h3, one_mul, sub_zero]
    exact mul_self_nonneg _)
  apply hu0
  funext p
  rcases p with e | v
  · exact congrFun h4 e
  · simpa [h3] using h5 v

/-- The polynomial of a network has at most as many real roots as the network has edges. -/
theorem card_aroots_pairPoly_le (N : Network V E) (ε : E → Bool) :
    ((N.pairPoly ε).aroots ℝ).toFinset.card ≤ Fintype.card E :=
  (Multiset.toFinset_card_le _).trans <| (card_roots' _).trans <|
    natDegree_map_le.trans (N.natDegree_pairPoly_le ε)

end Network

end Rectiling
