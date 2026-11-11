-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Elimination

/-!
# Solutions of the reduced system

Over a field in which no pivot vanishes, the equations recorded along a path have the same solutions as the equations of the system that has not been reduced, a form carried through the eliminations takes on a solution the value of the original form multiplied by the current pivot, and back-substitution in reverse order yields the solution with a given scale, which is unique.
-/

namespace Rectiling

namespace Fast

variable {R : Type} [CommRing R] {L : Type} [Field L] (ψ : R →+* L)

/-- The value of a form at an assignment of the unknowns of index below `N`. -/
def dot (N : ℕ) (F : Vec L) (v : ℕ → L) : L :=
  ∑ j ∈ Finset.range N, F j * v j

theorem dot_carryStep (N : ℕ) (e : Elim R) (F : Vec L) (v : ℕ → L) :
    dot N (carryStep ψ e F) v =
      (ψ (e.1 e.2.1) * dot N F v - F e.2.1 * dot N (mapVec ψ e.1) v) / ψ e.2.2 := by
  simp only [dot, carryStep, mapVec]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dot_update_of_zero {N : ℕ} {F : Vec L} {m : ℕ} (hF : F m = 0) (v : ℕ → L) (y : L) :
    dot N F (Function.update v m y) = dot N F v := by
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = m
  · subst hj
    simp [hF]
  · rw [Function.update_of_ne hj]

theorem dot_update {N : ℕ} (F : Vec L) {m : ℕ} (hm : m < N) (v : ℕ → L) (y : L) :
    dot N F (Function.update v m y) = ∑ j ∈ (Finset.range N).erase m, F j * v j + F m * y := by
  unfold dot
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hm), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem dot_eq_erase {N : ℕ} (F : Vec L) {m : ℕ} (hm : m < N) (v : ℕ → L) :
    dot N F v = ∑ j ∈ (Finset.range N).erase m, F j * v j + F m * v m := by
  conv_lhs => rw [← Function.update_eq_self m v]
  exact dot_update F hm v (v m)

/-! ### The eliminations seen so far -/

variable {ψ}

theorem Elims.length_eq {els : List (Elim R)} {ts : List (Vec R)} {π : R} (h : Elims ψ els ts π) :
    els.length = ts.length := by
  induction h with
  | nil => rfl
  | snoc _ _ _ ih => simp [ih]

/-- On a solution of the equations seen so far, a carried form takes the value of the original form multiplied by the current pivot. -/
theorem Elims.dot_carry {els : List (Elim R)} {ts : List (Vec R)} {π : R} (h : Elims ψ els ts π)
    {N : ℕ} {v : ℕ → L} (hv : ∀ t ∈ ts, dot N (mapVec ψ t) v = 0) :
    ∀ F : Vec L, dot N (carry ψ els F) v = ψ π * dot N F v := by
  induction h with
  | nil => intro F; simp
  | @snoc els ts π E e m _ hπ hE ih =>
    intro F
    have ih' := ih fun t ht => hv t (List.mem_append_left _ ht)
    rw [carry_concat, dot_carryStep]
    simp only
    rw [ih' F, hE, ih' (mapVec ψ e), hv e (by simp)]
    field_simp
    ring

/-- A carried form has no coefficient at an eliminated unknown. -/
theorem Elims.carry_pivot {els : List (Elim R)} {ts : List (Vec R)} {π : R}
    (h : Elims ψ els ts π) : ∀ (F : Vec L), ∀ e ∈ els, carry ψ els F e.2.1 = 0 := by
  induction h with
  | nil => intro F e he; simp at he
  | @snoc els ts π E e m _ hπ hE ih =>
    intro F e0 he0
    rw [carry_concat]
    simp only [carryStep]
    rcases List.mem_append.mp he0 with he0 | he0
    · have h1 := ih F e0 he0
      have h2 := ih (mapVec ψ e) e0 he0
      rw [← hE] at h2
      simp only [mapVec] at h2
      rw [h1, h2]
      simp
    · obtain rfl : e0 = (E, m, π) := by simpa using he0
      simp only
      rw [mul_comm, sub_self, zero_div]

/-- An equation recorded later has no coefficient at an unknown eliminated earlier. -/
theorem Elims.pairwise {els : List (Elim R)} {ts : List (Vec R)} {π : R} (h : Elims ψ els ts π) :
    els.Pairwise fun a b => ψ (b.1 a.2.1) = 0 := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @snoc els ts π E e m h' hπ hE ih =>
    refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    obtain rfl : b = (E, m, π) := by simpa using hb
    have := h'.carry_pivot (mapVec ψ e) a ha
    rw [← hE] at this
    exact this

/-- A solution of the recorded equations solves the equations that have not been reduced. -/
theorem Elims.true_of_stage {els : List (Elim R)} {ts : List (Vec R)} {π : R}
    (h : Elims ψ els ts π) {N : ℕ} {v : ℕ → L}
    (hv : ∀ e ∈ els, dot N (mapVec ψ e.1) v = 0) : ∀ t ∈ ts, dot N (mapVec ψ t) v = 0 := by
  induction h with
  | nil => intro t ht; simp at ht
  | @snoc els ts π E e m h' hπ hE ih =>
    have ih' := ih fun e he => hv e (List.mem_append_left _ he)
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ih' t ht
    · obtain rfl : t = e := by simpa using ht
      have h1 := hv (E, m, π) (by simp)
      simp only at h1
      rw [hE, h'.dot_carry ih'] at h1
      exact (mul_eq_zero.mp h1).resolve_left hπ

/-- A solution of the equations that have not been reduced solves the recorded equations. -/
theorem Elims.stage_of_true {els : List (Elim R)} {ts : List (Vec R)} {π : R}
    (h : Elims ψ els ts π) {N : ℕ} {v : ℕ → L}
    (hv : ∀ t ∈ ts, dot N (mapVec ψ t) v = 0) : ∀ e ∈ els, dot N (mapVec ψ e.1) v = 0 := by
  induction h with
  | nil => intro e he; simp at he
  | @snoc els ts π E e m h' hπ hE ih =>
    have hv' : ∀ t ∈ ts, dot N (mapVec ψ t) v = 0 := fun t ht => hv t (List.mem_append_left _ ht)
    intro e0 he0
    rcases List.mem_append.mp he0 with he0 | he0
    · exact ih hv' e0 he0
    · obtain rfl : e0 = (E, m, π) := by simpa using he0
      simp only
      rw [hE, h'.dot_carry hv', hv e (by simp), mul_zero]

/-! ### The records of a path -/

/-- The records of a path extend the eliminations seen so far; the last equation is the final one. -/
theorem Trace.elims {els : List (Elim R)} {π : R} {steps : List (Step R)} {ps es : List (Vec R)}
    {Efin : Vec R} (h : Trace ψ els π steps ps es Efin) :
    ∀ ts : List (Vec R), Elims ψ els ts π → ψ π ≠ 0 →
      ∃ (esI : List (Vec R)) (e : Vec R) (πf : R), es = esI ++ [e] ∧
        Elims ψ (els ++ Fast.elims steps) (ts ++ esI) πf ∧ ψ πf ≠ 0 ∧
        mapVec ψ Efin = carry ψ (els ++ Fast.elims steps) (mapVec ψ e) := by
  induction h with
  | @leaf els π mv size p e Efin hsize hfin =>
    intro ts hels hπ
    exact ⟨[], e, π, rfl, by simpa using hels, hπ, by simpa using hfin⟩
  | plain _ _ ih =>
    intro ts hels hπ
    simpa using ih ts hels hπ
  | @elim els π mv size p e E Efin m steps ps es hsize hE hπ' hEm _ ih =>
    intro ts hels hπ
    obtain ⟨esI, e', πf, rfl, h1, h2, h3⟩ := ih (ts ++ [e]) (hels.snoc hπ hE) hEm
    refine ⟨e :: esI, e', πf, rfl, ?_, h2, ?_⟩
    · simpa [List.append_assoc] using h1
    · simpa [List.append_assoc] using h3

/-- The size recorded for each placement is the positivity constraint of the placement, carried through the eliminations made before it. -/
theorem Trace.size {els : List (Elim R)} {π : R} {steps : List (Step R)} {ps es : List (Vec R)}
    {Efin : Vec R} (h : Trace ψ els π steps ps es Efin) :
    ps.length = steps.length ∧ ∀ (q : ℕ) (s : Step R), steps[q]? = some s →
      ∃ p, ps[q]? = some p ∧
        mapVec ψ s.size = carry ψ (els ++ Fast.elims (steps.take q)) (mapVec ψ p) := by
  induction h with
  | @leaf els π mv size p e Efin hsize hfin =>
    refine ⟨rfl, fun q s hs => ?_⟩
    cases q with
    | zero =>
      obtain rfl : _ = s := by simpa using hs
      exact ⟨p, rfl, by simpa using hsize⟩
    | succ q => simp at hs
  | @plain els π mv size p Efin steps ps es hsize _ ih =>
    refine ⟨by simp [ih.1], fun q s hs => ?_⟩
    cases q with
    | zero =>
      obtain rfl : _ = s := by simpa using hs
      exact ⟨p, rfl, by simpa using hsize⟩
    | succ q =>
      obtain ⟨p', hp', h'⟩ := ih.2 q s (by simpa using hs)
      exact ⟨p', by simpa using hp', by simpa using h'⟩
  | @elim els π mv size p e E Efin m steps ps es hsize hE hπ' hEm _ ih =>
    refine ⟨by simp [ih.1], fun q s hs => ?_⟩
    cases q with
    | zero =>
      obtain rfl : _ = s := by simpa using hs
      exact ⟨p, rfl, by simpa using hsize⟩
    | succ q =>
      obtain ⟨p', hp', h'⟩ := ih.2 q s (by simpa using hs)
      exact ⟨p', by simpa using hp', by simpa [List.append_assoc] using h'⟩

/-! ### Back-substitution -/

variable (ψ)

/-- The value that an equation gives to its eliminated unknown, from the values of the other unknowns. -/
def backStep (N : ℕ) (e : Elim R) (v : ℕ → L) : ℕ → L :=
  Function.update v e.2.1
    (-(∑ j ∈ (Finset.range N).erase e.2.1, ψ (e.1 j) * v j) / ψ (e.1 e.2.1))

/-- Back-substitution through the recorded equations, in reverse order. -/
def back (N : ℕ) (els : List (Elim R)) (v0 : ℕ → L) : ℕ → L :=
  els.foldr (backStep ψ N) v0

theorem back_cons (N : ℕ) (e : Elim R) (rest : List (Elim R)) (v0 : ℕ → L) :
    back ψ N (e :: rest) v0 =
      Function.update (back ψ N rest v0) e.2.1
        (-(∑ j ∈ (Finset.range N).erase e.2.1, ψ (e.1 j) * back ψ N rest v0 j) / ψ (e.1 e.2.1)) :=
  rfl

theorem back_of_not_mem (N : ℕ) (els : List (Elim R)) (v0 : ℕ → L) {j : ℕ}
    (hj : ∀ e ∈ els, e.2.1 ≠ j) : back ψ N els v0 j = v0 j := by
  induction els with
  | nil => rfl
  | cons e rest ih =>
    have h1 : e.2.1 ≠ j := hj e (by simp)
    rw [back_cons]
    rw [Function.update_of_ne (Ne.symm h1)]
    exact ih fun e' he' => hj e' (by simp [he'])

/-- Back-substitution solves the recorded equations. -/
theorem back_solves {N : ℕ} {els : List (Elim R)}
    (hpw : els.Pairwise fun a b => ψ (b.1 a.2.1) = 0) (hm : ∀ e ∈ els, e.2.1 < N)
    (hp : ∀ e ∈ els, ψ (e.1 e.2.1) ≠ 0) (v0 : ℕ → L) :
    ∀ e ∈ els, dot N (mapVec ψ e.1) (back ψ N els v0) = 0 := by
  induction els with
  | nil => intro e he; simp at he
  | cons e rest ih =>
    obtain ⟨hzero, hpw'⟩ := List.pairwise_cons.mp hpw
    have ih' := ih hpw' (fun e' he' => hm e' (by simp [he'])) (fun e' he' => hp e' (by simp [he']))
    intro e' he'
    rw [back_cons]
    rcases List.mem_cons.mp he' with rfl | he'
    · rw [dot_update _ (hm e' (by simp))]
      have := hp e' (by simp)
      simp only [mapVec]
      field_simp
      ring
    · rw [dot_update_of_zero (hzero e' he')]
      exact ih' e' he'

/-- An assignment that solves the recorded equations agrees with back-substitution at every eliminated unknown, if every unknown but the scale is eliminated. -/
theorem back_unique {N : ℕ} {v0 w : ℕ → L} (hw0 : v0 0 = w 0) :
    ∀ (rest pre : List (Elim R)), (pre ++ rest).Pairwise (fun a b => ψ (b.1 a.2.1) = 0) →
      (∀ e ∈ rest, e.2.1 < N) → (∀ e ∈ rest, ψ (e.1 e.2.1) ≠ 0) → (∀ e ∈ rest, e.2.1 ≠ 0) →
      (∀ j < N, j = 0 ∨ (∃ e ∈ pre, e.2.1 = j) ∨ ∃ e ∈ rest, e.2.1 = j) →
      (∀ e ∈ rest, dot N (mapVec ψ e.1) w = 0) →
      ∀ e ∈ rest, back ψ N rest v0 e.2.1 = w e.2.1 := by
  intro rest
  induction rest with
  | nil => intro pre _ _ _ _ _ _ e he; simp at he
  | cons e rest ih =>
    intro pre hpw hm hp h0 hcov hw
    have hpw' : ((pre ++ [e]) ++ rest).Pairwise (fun a b => ψ (b.1 a.2.1) = 0) := by
      simpa [List.append_assoc] using hpw
    have ih' := ih (pre ++ [e]) hpw' (fun e' he' => hm e' (by simp [he']))
      (fun e' he' => hp e' (by simp [he'])) (fun e' he' => h0 e' (by simp [he']))
      (fun j hj => by
        rcases hcov j hj with h | ⟨e', he', h⟩ | ⟨e', he', h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨e', by simp [he'], h⟩)
        · rcases List.mem_cons.mp he' with rfl | he'
          · exact Or.inr (Or.inl ⟨e', by simp, h⟩)
          · exact Or.inr (Or.inr ⟨e', he', h⟩))
      (fun e' he' => hw e' (by simp [he']))
    have hu0 : back ψ N rest v0 0 = w 0 := by
      rw [back_of_not_mem ψ N rest v0 fun e' he' => h0 e' (by simp [he']), hw0]
    have hmN := hm e (by simp)
    have hpe := hp e (by simp)
    have hsum : ∑ j ∈ (Finset.range N).erase e.2.1, ψ (e.1 j) * back ψ N rest v0 j =
        ∑ j ∈ (Finset.range N).erase e.2.1, ψ (e.1 j) * w j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hjm, hjN⟩ := Finset.mem_erase.mp hj
      rcases hcov j (Finset.mem_range.mp hjN) with h | ⟨e', he', h⟩ | ⟨e', he', h⟩
      · rw [h, hu0]
      · have hz := (List.pairwise_append.mp hpw).2.2 e' he' e (by simp)
        rw [h] at hz
        rw [hz, zero_mul, zero_mul]
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact absurd h (Ne.symm hjm)
        · rw [← h, ih' e' he']
    have hwe := hw e (by simp)
    rw [dot_eq_erase _ hmN] at hwe
    simp only [mapVec] at hwe
    intro e' he'
    rw [back_cons]
    by_cases hmm : e'.2.1 = e.2.1
    · rw [hmm, Function.update_self, hsum]
      field_simp
      linear_combination -hwe
    · rw [Function.update_of_ne hmm]
      rcases List.mem_cons.mp he' with rfl | he'
      · exact absurd rfl hmm
      · exact ih' e' he'

omit [CommRing R] in
/-- Distinct eliminated unknowns, as many as there are sides, are all the sides. -/
theorem covers {els : List (Elim R)} {k : ℕ} (hnd : (els.map fun e => e.2.1).Nodup)
    (hr : ∀ e ∈ els, 1 ≤ e.2.1 ∧ e.2.1 ≤ k) (hlen : els.length = k) {j : ℕ} (h1 : 1 ≤ j)
    (hk : j ≤ k) : ∃ e ∈ els, e.2.1 = j := by
  have hsub : (els.map fun e => e.2.1).toFinset ⊆ Finset.Icc 1 k := by
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    exact Finset.mem_Icc.mpr (hr e he)
  have hcard : (Finset.Icc 1 k).card ≤ (els.map fun e => e.2.1).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen, Nat.card_Icc]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hj : j ∈ (els.map fun e => e.2.1).toFinset := by
    rw [heq]
    exact Finset.mem_Icc.mpr ⟨h1, hk⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
  exact ⟨e, he, rfl⟩

/-- The eliminated unknowns are distinct. -/
theorem nodup_pivots {els : List (Elim R)} (hpw : els.Pairwise fun a b => ψ (b.1 a.2.1) = 0)
    (hp : ∀ e ∈ els, ψ (e.1 e.2.1) ≠ 0) : (els.map fun e => e.2.1).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  refine hpw.imp_of_mem ?_
  intro a b _ hb hab heq
  rw [heq] at hab
  exact hp b hb hab

end Fast

end Rectiling
