-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Fast

/-!
# Exactness of the divisions

The divisions of the eager elimination are exact, as in Bareiss's algorithm: the pivot current after a number of eliminations is the minor of the system on the eliminated unknowns (`Elims.pivot_eq_det`), and each coefficient of a form after an elimination is such a minor of the system bordered by the form, hence lies in the ring of coefficients (`Elims.divisible`).
At every stage that the symbolic pass reaches, the check of exactness therefore succeeds (`division_exact`).

The correctness of the default method does not depend on this module, since the model passes a path to the reference method when a division is not exact.
-/

namespace Rectiling

namespace Fast

section Minor

variable {R : Type} [CommRing R] {L : Type} [Field L] {ψ : R →+* L}

open Matrix in
/-- **The pivot is a minor.** The current pivot is the determinant of the equations that have not been reduced, restricted to the eliminated unknowns in the order of their elimination. -/
theorem Elims.pivot_eq_det {els : List (Elim R)} {ts : List (Vec R)} {π : R}
    (h : Elims ψ els ts π) :
    ψ π = (Matrix.of fun i l : Fin els.length =>
      ψ (ts.getD i 0 (els.getD l noElim).2.1)).det := by
  set n := els.length with hn
  set A : Matrix (Fin n) (Fin n) L :=
    Matrix.of fun i l => ψ (ts.getD i 0 (els.getD l noElim).2.1) with hA
  let B : Matrix (Fin n) (Fin n) L :=
    Matrix.of fun i l => ψ ((els.getD i noElim).1 (els.getD l noElim).2.1)
  have hrow : ∀ i : Fin n, ∃ c : ℕ → L, ∀ j,
      ψ ((els.getD i noElim).1 j) = ψ (els.getD i noElim).2.2 * ψ (ts.getD i 0 j) +
        ∑ l ∈ Finset.range i, c l * ψ (ts.getD l 0 j) := fun i => (h.row i i.isLt).2
  choose c hc using hrow
  let T : Matrix (Fin n) (Fin n) L := Matrix.of fun i l =>
    (if (l : ℕ) < i then c i l else 0) + if l = i then ψ (els.getD i noElim).2.2 else 0
  have hBT : B = T * A := by
    ext i j
    simp only [B, T, A, Matrix.mul_apply, Matrix.of_apply]
    rw [hc i]
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    rw [add_comm]
    congr 1
    rw [Fin.sum_univ_eq_sum_range
      (fun l => if l < (i : ℕ) then c i l * ψ (ts.getD l 0 (els.getD j noElim).2.1) else 0) n,
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
      have h2 : l ≠ i := ne_of_gt hil'
      have h3 : ¬ l < i := not_lt.mpr hil'.le
      simp [T, h2, h3]
  have hgetD : ∀ i : Fin n, els.getD i noElim = els[(i : ℕ)]'i.isLt := fun i =>
    List.getD_eq_getElem _ _ i.isLt
  have hB : B.det = ∏ i : Fin n, ψ ((els.getD i noElim).1 (els.getD i noElim).2.1) := by
    rw [Matrix.det_of_isUpperTriangular]
    · rfl
    · intro i l hli
      have hli' : (l : ℕ) < i := hli
      have := List.pairwise_iff_getElem.mp h.pairwise l i l.isLt i.isLt hli'
      simp only [B, Matrix.of_apply]
      rw [hgetD, hgetD]
      exact this
  rw [hBT, Matrix.det_mul, hT] at hB
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
  rw [hprod1, hprod2, htel] at hB
  have key : (∏ i ∈ Finset.range n, ψ (pivotAt els π i)) * (ψ π - A.det) = 0 := by
    linear_combination -hB
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

/-- An elimination record with its coefficients mapped by a ring homomorphism. -/
def mapElim (ψ : R →+* L) (e : Elim R) : Elim L :=
  (mapVec ψ e.1, e.2.1, ψ e.2.2)

theorem carry_mapElim (ψ : R →+* L) (els : List (Elim R)) (G : Vec L) :
    carry (RingHom.id L) (els.map (mapElim ψ)) G = carry ψ els G := by
  unfold carry
  rw [List.foldl_map]
  rfl

/-- The eliminations seen so far, with their records mapped into the field. -/
theorem Elims.mapRecords {els : List (Elim R)} {ts : List (Vec R)} {π : R}
    (h : Elims ψ els ts π) :
    Elims (RingHom.id L) (els.map (mapElim ψ)) (ts.map (mapVec ψ)) (ψ π) := by
  induction h with
  | nil => simpa using (Elims.nil : Elims (RingHom.id L) [] [] 1)
  | @snoc els ts π E e m _ hπ hE ih =>
    rw [List.map_append, List.map_append]
    refine Elims.snoc (E := mapVec ψ E) (e := mapVec ψ e) (m := m) ih hπ ?_
    rw [carry_mapElim]
    exact hE

/-- **Exactness of the divisions.** If the ring of coefficients embeds in the field, the elimination of an unknown from a form at the current stage divides exactly by the current pivot. -/
theorem Elims.divisible (hinj : Function.Injective ψ) {els : List (Elim R)} {ts : List (Vec R)}
    {π : R} (h : Elims ψ els ts π) (hπ : ψ π ≠ 0) {E e : Vec R} (m : ℕ)
    (hE : mapVec ψ E = carry ψ els (mapVec ψ e)) (hEm : E m ≠ 0) {F Ft : Vec R}
    (hF : mapVec ψ F = carry ψ els (mapVec ψ Ft)) : Divisible (E, m, π) F := by
  intro j
  have hEm' : ψ (E m) ≠ 0 := (map_ne_zero_iff ψ hinj).mpr hEm
  -- the eliminations, followed by a fictitious one of the unknown `j` from the form
  have h1 : Elims ψ (els ++ [(E, m, π)]) (ts ++ [e]) (E m) := h.snoc hπ hE
  have h2 := h1.mapRecords
  set G : Vec L := carry ψ (els ++ [(E, m, π)]) (mapVec ψ Ft) with hG
  have h3 : Elims (RingHom.id L) ((els ++ [(E, m, π)]).map (mapElim ψ) ++ [(G, j, ψ (E m))])
      ((ts ++ [e]).map (mapVec ψ) ++ [mapVec ψ Ft]) (G j) :=
    h2.snoc (E := G) (e := mapVec ψ Ft) (m := j) hEm' (by
      rw [carry_mapElim]
      rfl)
  have hdet := h3.pivot_eq_det
  -- the minor has its entries in the ring
  set elsL := (els ++ [(E, m, π)]).map (mapElim ψ) ++ [(G, j, ψ (E m))] with helsL
  have hts : (ts ++ [e]).map (mapVec ψ) ++ [mapVec ψ Ft] = (ts ++ [e] ++ [Ft]).map (mapVec ψ) := by
    simp
  have hentry : (Matrix.of fun i l : Fin elsL.length =>
      (RingHom.id L) (((ts ++ [e]).map (mapVec ψ) ++ [mapVec ψ Ft]).getD i 0
        (elsL.getD l noElim).2.1)) =
      ψ.mapMatrix (Matrix.of fun i l : Fin elsL.length =>
        (ts ++ [e] ++ [Ft]).getD i 0 (elsL.getD l noElim).2.1) := by
    ext i l
    have hzero : (0 : Vec L) = mapVec ψ 0 := by
      funext k
      simp [mapVec]
    simp only [Matrix.of_apply, RingHom.id_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hts, hzero, List.getD_map]
    rfl
  rw [hentry, ← RingHom.map_det] at hdet
  -- the coefficient after the elimination is the minor
  have hGj : G j = ψ (elimNum E m F j) / ψ π := by
    rw [hG, carry_concat, ← hF]
    simp [carryStep, mapVec, elimNum]
  rw [RingHom.id_apply, hGj, div_eq_iff hπ, ← map_mul] at hdet
  exact Dvd.intro_left _ (hinj hdet).symm

end Minor

/-! ### The stages of the symbolic pass -/

section Stages

variable {R : Type} [CommRing R] {L : Type} [Field L] (ψ : R →+* L) (X : Rˣ)

/-- The forms of a stage are the forms of a staircase that has not been reduced, carried through the eliminations seen so far. -/
def Stage.Linked (st : Stage R) : Prop :=
  ∃ (els : List (Elim R)) (ts : List (Vec R)) (sT : List (Tier (Vec R))),
    Elims ψ els ts st.pivot ∧ ψ st.pivot ≠ 0 ∧
    st.stairs.map (Tier.map (mapVec ψ)) = sT.map (Tier.map fun F => carry ψ els (mapVec ψ F)) ∧
    ∀ u, st.count < u → carry ψ els (mapVec ψ (unitVec u)) =
      fun j => ψ st.pivot * mapVec ψ (unitVec u) j

theorem Stage.linked_init (a b : ℤ) : (Stage.init a b : Stage R).Linked ψ :=
  ⟨[], [], homInitial a b, Elims.nil, by simp [Stage.init], rfl, by
    intro u _
    funext j
    simp [Stage.init]⟩

variable {ψ X}

/-- At a linked stage, the elimination that follows a full placement divides exactly. -/
theorem Stage.Linked.divisible (hinj : Function.Injective ψ) {st : Stage R}
    (h : st.Linked ψ) {mv : Placement} {E : Vec R}
    (heq : equationAt (vecAlgebra X) st.stairs mv = some E) {m : ℕ} (hEm : E m ≠ 0) :
    ∀ t ∈ place (vecAlgebra X) st.stairs mv st.side,
      Divisible (E, m, st.pivot) t.floor ∧ Divisible (E, m, st.pivot) t.wall := by
  obtain ⟨els, ts, sT, hEl, hπ, hst, hfresh⟩ := h
  obtain ⟨hnext, -, hequ⟩ := step_link ψ X hst hfresh mv
  rw [heq] at hequ
  obtain ⟨e, -, he'⟩ := Option.map_eq_some_iff.mp hequ.symm
  intro t ht
  have hmem : Tier.map (mapVec ψ) t ∈
      (place (vecAlgebra X) sT mv (trueFresh st.count)).map
        (Tier.map fun F => carry ψ els (mapVec ψ F)) := by
    rw [← hnext]
    exact List.mem_map_of_mem ht
  obtain ⟨tT, -, htT⟩ := List.mem_map.mp hmem
  have hfloor : mapVec ψ t.floor = carry ψ els (mapVec ψ tT.floor) :=
    (congrArg Tier.floor htT).symm
  have hwall : mapVec ψ t.wall = carry ψ els (mapVec ψ tT.wall) :=
    (congrArg Tier.wall htT).symm
  exact ⟨hEl.divisible hinj hπ m he'.symm hEm hfloor, hEl.divisible hinj hπ m he'.symm hEm hwall⟩

/-- A placement without elimination leads from a linked stage to a linked stage. -/
theorem Stage.Linked.plain {st : Stage R} (h : st.Linked ψ) (mv : Placement) :
    (⟨place (vecAlgebra X) st.stairs mv st.side, st.pivot, nextIndex st.count mv⟩ :
      Stage R).Linked ψ := by
  obtain ⟨els, ts, sT, hEl, hπ, hst, hfresh⟩ := h
  obtain ⟨hnext, -, -⟩ := step_link ψ X hst hfresh mv
  exact ⟨els, ts, _, hEl, hπ, hnext, fun u hu =>
    hfresh u (lt_of_le_of_lt (le_nextIndex _ _) hu)⟩

/-- A placement followed by an exact elimination leads from a linked stage to a linked stage. -/
theorem Stage.Linked.elim (hinj : Function.Injective ψ) {st : Stage R} (h : st.Linked ψ)
    {mv : Placement} {E : Vec R} (heq : equationAt (vecAlgebra X) st.stairs mv = some E)
    {m : ℕ} (hm : m ≤ nextIndex st.count mv) (hEm : E m ≠ 0) :
    (⟨(place (vecAlgebra X) st.stairs mv st.side).map (Tier.map (elimForm (E, m, st.pivot))),
      E m, nextIndex st.count mv⟩ : Stage R).Linked ψ := by
  have hdiv := h.divisible (X := X) hinj heq hEm
  obtain ⟨els, ts, sT, hEl, hπ, hst, hfresh⟩ := h
  obtain ⟨hnext, -, hequ⟩ := step_link ψ X hst hfresh mv
  rw [heq] at hequ
  obtain ⟨e, -, he'⟩ := Option.map_eq_some_iff.mp hequ.symm
  have hEm' : ψ (E m) ≠ 0 := (map_ne_zero_iff ψ hinj).mpr hEm
  refine ⟨els ++ [(E, m, st.pivot)], ts ++ [e], place (vecAlgebra X) sT mv (trueFresh st.count),
    hEl.snoc hπ he'.symm, hEm', ?_, ?_⟩
  · rw [List.map_map]
    have h1 : ∀ t ∈ place (vecAlgebra X) st.stairs mv st.side,
        (Tier.map (mapVec ψ) ∘ Tier.map (elimForm (E, m, st.pivot))) t =
          (Tier.map (carryStep ψ (E, m, st.pivot)) ∘ Tier.map (mapVec ψ)) t := by
      intro t ht
      obtain ⟨hf, hw⟩ := hdiv t ht
      simp only [Function.comp_apply, Tier.map, mapVec_elimForm ψ hπ hf,
        mapVec_elimForm ψ hπ hw]
    rw [List.map_congr_left h1, ← List.map_map, hnext, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Tier.map, carry_concat]
  · intro u hu
    have hu' : nextIndex st.count mv < u := hu
    rw [carry_concat, hfresh u (lt_of_le_of_lt (le_nextIndex _ _) hu')]
    funext j
    have hmu : m ≠ u := by omega
    simp only [carryStep, mapVec, unitVec, hmu, ite_false, map_zero, mul_zero, zero_mul,
      sub_zero]
    field_simp

end Stages

/-! ### The model -/

/-- The stages that the symbolic pass reaches, with the placements made. -/
inductive Reached (M : Limits) (a b : ℤ) : List Placement → Stage Coeff → Prop
  | init : Reached M a b [] (Stage.init a b)
  | step {done : List Placement} {st st' : Stage Coeff} {mv : Placement} {s : Step Coeff}
      (h : Reached M a b done st) (hadv : advance M st done mv = .next st' s) :
      Reached M a b (done ++ [mv]) st'

theorem Reached.linked {M : Limits} {a b : ℤ} {done : List Placement} {st : Stage Coeff}
    (h : Reached M a b done st) :
    st.Linked (algebraMap Coeff (FractionRing Coeff)) := by
  have hinj : Function.Injective (algebraMap Coeff (FractionRing Coeff)) :=
    IsFractionRing.injective Coeff (FractionRing Coeff)
  induction h with
  | init => exact Stage.linked_init _ a b
  | step _ hadv ih =>
    rcases (advance_next hadv).2 with ⟨size, -, -, -, rfl⟩ |
      ⟨size, E, m, -, heq, -, hm, hEm, -, -, rfl⟩
    · exact ih.plain _
    · exact ih.elim hinj heq hm hEm

/-- **The check of exactness never fails.** At every stage that the symbolic pass reaches, for every full placement and every unknown with a non-zero coefficient in its equation, the elimination divides every floor and wall exactly. -/
theorem division_exact {M : Limits} {a b : ℤ} {done : List Placement} {st : Stage Coeff}
    (h : Reached M a b done st) {mv : Placement} {E : Vec Coeff}
    (heq : equationAt (vecAlgebra propX) st.stairs mv = some E) {m : ℕ} (hEm : E m ≠ 0) :
    ∀ t ∈ place (vecAlgebra propX) st.stairs mv st.side,
      Divisible (E, m, st.pivot) t.floor ∧ Divisible (E, m, st.pivot) t.wall :=
  h.linked.divisible (IsFractionRing.injective Coeff (FractionRing Coeff)) heq hEm

end Fast

end Rectiling
