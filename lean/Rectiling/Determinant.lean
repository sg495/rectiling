-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.BackSubstitution

/-!
# The last pivot is the determinant

The pivot current after the elimination of every unknown is, up to sign, the determinant of the system that has not been reduced.
The recorded equations are the rows of the product of a lower triangular matrix, whose diagonal holds the previous pivots, with the matrix of the system; after a permutation of the columns they form an upper triangular matrix, whose diagonal holds the pivots.
-/

namespace Rectiling

namespace Fast

variable {R : Type} [CommRing R] {L : Type} [Field L] {ψ : R →+* L}

/-- The record standing for a missing elimination. -/
def noElim : Elim R :=
  (0, 0, 0)

/-- A carried form is the original form multiplied by the current pivot, plus a combination of the equations seen so far. -/
theorem Elims.carry_eq {els : List (Elim R)} {ts : List (Vec R)} {π : R} (h : Elims ψ els ts π) :
    ∀ F : Vec L, ∃ c : ℕ → L, ∀ j,
      carry ψ els F j = ψ π * F j + ∑ l ∈ Finset.range ts.length, c l * ψ (ts.getD l 0 j) := by
  induction h with
  | nil => intro F; exact ⟨fun _ => 0, fun j => by simp⟩
  | @snoc els ts π E e m _ hπ hE ih =>
    intro F
    obtain ⟨c, hc⟩ := ih F
    obtain ⟨d, hd⟩ := ih (mapVec ψ e)
    refine ⟨fun l => if l < ts.length then
      (ψ (E m) * c l - carry ψ els F m * d l) / ψ π else -carry ψ els F m, fun j => ?_⟩
    have hEj : ψ (E j) = carry ψ els (mapVec ψ e) j := congrFun hE j
    rw [carry_concat]
    simp only [carryStep]
    rw [hEj, hc j, hd j, List.length_append, List.length_singleton, Finset.sum_range_succ]
    have hlast : (ts ++ [e]).getD ts.length 0 = e := by
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    have hsum : ∑ l ∈ Finset.range ts.length,
        (if l < ts.length then (ψ (E m) * c l - carry ψ els F m * d l) / ψ π
          else -carry ψ els F m) * ψ ((ts ++ [e]).getD l 0 j) =
        (ψ (E m) * ∑ l ∈ Finset.range ts.length, c l * ψ (ts.getD l 0 j) -
          carry ψ els F m * ∑ l ∈ Finset.range ts.length, d l * ψ (ts.getD l 0 j)) / ψ π := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      rw [List.getD_append _ _ _ _ hl']
      simp only [hl', ↓reduceIte]
      ring
    rw [hsum, hlast]
    simp only [lt_irrefl, ↓reduceIte, mapVec]
    field_simp
    ring

/-- Each recorded equation is its original multiplied by the previous pivot, which does not vanish, plus a combination of the earlier originals. -/
theorem Elims.row {els : List (Elim R)} {ts : List (Vec R)} {π : R} (h : Elims ψ els ts π) :
    ∀ i < els.length, ψ (els.getD i noElim).2.2 ≠ 0 ∧ ∃ c : ℕ → L, ∀ j,
      ψ ((els.getD i noElim).1 j) = ψ (els.getD i noElim).2.2 * ψ (ts.getD i 0 j) +
        ∑ l ∈ Finset.range i, c l * ψ (ts.getD l 0 j) := by
  induction h with
  | nil => intro i hi; simp at hi
  | @snoc els ts π E e m h' hπ hE ih =>
    intro i hi
    have hlen := h'.length_eq
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · obtain ⟨h1, c, hc⟩ := ih i hi
      rw [List.getD_append _ _ _ _ hi]
      refine ⟨h1, c, fun j => ?_⟩
      rw [hc j, List.getD_append _ _ _ _ (hlen ▸ hi)]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [List.getD_append _ _ _ _ (by have := Finset.mem_range.mp hl; omega)]
    · have h1 : (els ++ [(E, m, π)]).getD els.length noElim = (E, m, π) := by
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      have h2 : (ts ++ [e]).getD els.length 0 = e := by
        rw [hlen, List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      rw [h1, h2]
      obtain ⟨c, hc⟩ := h'.carry_eq (mapVec ψ e)
      refine ⟨hπ, c, fun j => ?_⟩
      have hEj : ψ (E j) = carry ψ els (mapVec ψ e) j := congrFun hE j
      simp only
      rw [hEj, hc j, hlen]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hl)]

/-- The pivot previous to the elimination of the given index, and the current pivot beyond the last. -/
def pivotAt (els : List (Elim R)) (π : R) (i : ℕ) : R :=
  if i < els.length then (els.getD i noElim).2.2 else π

/-- The first pivot is one, and each elimination makes the coefficient of its eliminated unknown the next pivot. -/
theorem Elims.chain {els : List (Elim R)} {ts : List (Vec R)} {π : R} (h : Elims ψ els ts π) :
    pivotAt els π 0 = 1 ∧ ∀ i < els.length,
      (els.getD i noElim).1 (els.getD i noElim).2.1 = pivotAt els π (i + 1) := by
  induction h with
  | nil => exact ⟨rfl, fun i hi => by simp at hi⟩
  | @snoc els ts π E e m h' hπ hE ih =>
    have hsame : ∀ i ≤ els.length, pivotAt (els ++ [(E, m, π)]) (E m) i = pivotAt els π i := by
      intro i hi
      unfold pivotAt
      have hlt : i < els.length + 1 := by omega
      rw [List.length_append, List.length_singleton]
      simp only [hlt, ↓reduceIte]
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · simp only [hi, ↓reduceIte]
        rw [List.getD_append _ _ _ _ hi]
      · simp only [lt_irrefl, ↓reduceIte]
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp
    refine ⟨by rw [hsame 0 (Nat.zero_le _)]; exact ih.1, fun i hi => ?_⟩
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getD_append _ _ _ _ hi, hsame (i + 1) hi]
      exact ih.2 i hi
    · have h1 : (els ++ [(E, m, π)]).getD els.length noElim = (E, m, π) := by
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      rw [h1]
      simp [pivotAt]

open Matrix in
/-- **The last pivot is the determinant.** If the eliminated unknowns are distinct and as many as the equations, the current pivot is, up to sign, the determinant of the equations that have not been reduced. -/
theorem Elims.det_eq {els : List (Elim R)} {ts : List (Vec R)} {π : R} (h : Elims ψ els ts π)
    (hm : ∀ e ∈ els, e.2.1 < els.length) (hnd : (els.map fun e => e.2.1).Nodup) :
    ∃ s : ℤˣ, ψ π = ((s : ℤ) : L) *
      (Matrix.of fun i j : Fin els.length => ψ (ts.getD i 0 j)).det := by
  set n := els.length with hn
  set A : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => ψ (ts.getD i 0 j) with hA
  let B : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => ψ ((els.getD i noElim).1 j)
  have hrow : ∀ i : Fin n, ∃ c : ℕ → L, ∀ j,
      ψ ((els.getD i noElim).1 j) = ψ (els.getD i noElim).2.2 * ψ (ts.getD i 0 j) +
        ∑ l ∈ Finset.range i, c l * ψ (ts.getD l 0 j) := fun i => (h.row i i.isLt).2
  choose c hc using hrow
  let T : Matrix (Fin n) (Fin n) L := Matrix.of fun i l =>
    (if (l : ℕ) < i then c i l else 0) + if l = i then ψ (els.getD i noElim).2.2 else 0
  have hBT : B = T * A := by
    ext i j
    simp only [B, T, A, Matrix.mul_apply, Matrix.of_apply]
    rw [hc i j]
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    rw [add_comm]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun l => if l < (i : ℕ) then c i l * ψ (ts.getD l 0 j) else 0) n,
      ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    have := i.isLt
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hT : T.det = ∏ i : Fin n, ψ (els.getD i noElim).2.2 := by
    rw [Matrix.det_of_isLowerTriangular T]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [T]
    · intro i l hil
      have hil' : i < l := hil
      have h1 : ¬ ((l : ℕ) < i) := by
        have : (i : ℕ) < l := hil'
        omega
      have h2 : l ≠ i := ne_of_gt hil'
      have h3 : ¬ l < i := not_lt.mpr hil'.le
      simp [T, h2, h3]
  have hgetD : ∀ i : Fin n, els.getD i noElim = els[(i : ℕ)]'i.isLt := fun i =>
    List.getD_eq_getElem _ _ i.isLt
  let σf : Fin n → Fin n := fun i => ⟨(els.getD i noElim).2.1, by
    rw [hgetD]
    exact hm _ (List.getElem_mem _)⟩
  have hinj : Function.Injective σf := by
    intro i l hil
    have h1 : (els.getD i noElim).2.1 = (els.getD l noElim).2.1 := congrArg Fin.val hil
    rw [hgetD, hgetD] at h1
    have hi' : (i : ℕ) < (els.map fun e => e.2.1).length := by
      rw [List.length_map]
      exact i.isLt
    have hl' : (l : ℕ) < (els.map fun e => e.2.1).length := by
      rw [List.length_map]
      exact l.isLt
    have h2 : (els.map fun e => e.2.1)[(i : ℕ)]'hi' = (els.map fun e => e.2.1)[(l : ℕ)]'hl' := by
      simpa using h1
    exact Fin.ext ((hnd.getElem_inj_iff).mp h2)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hinj)
  have hB' : (B.submatrix id σ).det = ∏ i : Fin n,
      ψ ((els.getD i noElim).1 (els.getD i noElim).2.1) := by
    rw [Matrix.det_of_isUpperTriangular]
    · rfl
    · intro i l hli
      have hli' : (l : ℕ) < i := hli
      have := List.pairwise_iff_getElem.mp h.pairwise l i l.isLt i.isLt hli'
      simp only [Matrix.submatrix_apply, id, B, Matrix.of_apply, σ, Equiv.ofBijective_apply, σf]
      rw [hgetD, hgetD]
      exact this
  rw [Matrix.det_permute', hBT, Matrix.det_mul, hT] at hB'
  obtain ⟨h0, hchain⟩ := h.chain
  have hprod1 : ∏ i : Fin n, ψ ((els.getD i noElim).1 (els.getD i noElim).2.1) =
      ∏ i ∈ Finset.range n, ψ (pivotAt els π (i + 1)) := by
    rw [Fin.prod_univ_eq_prod_range
      (fun i => ψ ((els.getD i noElim).1 (els.getD i noElim).2.1)) n]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hchain i (Finset.mem_range.mp hi)]
  have hprod2 : ∏ i : Fin n, ψ (els.getD i noElim).2.2 =
      ∏ i ∈ Finset.range n, ψ (pivotAt els π i) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ψ (els.getD i noElim).2.2) n]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [pivotAt, hn ▸ hi', ↓reduceIte]
  have htel : ∏ i ∈ Finset.range n, ψ (pivotAt els π (i + 1)) =
      (∏ i ∈ Finset.range n, ψ (pivotAt els π i)) * ψ π := by
    have h1 := Finset.prod_range_succ' (fun i => ψ (pivotAt els π i)) n
    have h2 := Finset.prod_range_succ (fun i => ψ (pivotAt els π i)) n
    rw [h1, h0, map_one, mul_one] at h2
    rw [h2]
    simp [pivotAt, hn]
  have hne : ∏ i ∈ Finset.range n, ψ (pivotAt els π i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [pivotAt, hn ▸ hi', ↓reduceIte]
    exact (h.row i hi').1
  rw [hprod1, hprod2, htel] at hB'
  refine ⟨Equiv.Perm.sign σ, ?_⟩
  have key : (∏ i ∈ Finset.range n, ψ (pivotAt els π i)) *
      (ψ π - (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : L) * A.det) = 0 := by
    linear_combination -hB'
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Fast

end Rectiling
