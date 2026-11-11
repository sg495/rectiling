-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Staircase

/-!
# Eager fraction-free elimination

Model of the symbolic pass of `src/fast.rs`: linear forms in the scale of the main rectangle and the free tile sides, the elimination of one unknown after each full placement, and the relation between the forms at each stage of elimination and the forms of the system that has not been reduced.

The coefficient ring is any commutative ring with a distinguished unit, the tile proportion.
Unknown zero is the scale; unknown `j + 1` is the free side of the inside placement of index `j`.
-/

namespace Rectiling

namespace Fast

/-- Linear form in the scale and the free sides, by index of unknown. -/
abbrev Vec (R : Type) := ℕ → R

section Forms

variable {R : Type} [CommRing R]

/-- The form consisting of one unknown. -/
def unitVec (u : ℕ) : Vec R :=
  fun j => if j = u then 1 else 0

/-- The arithmetic of linear forms, for the given proportion. -/
def vecAlgebra (X : Rˣ) : Algebra (Vec R) :=
  ⟨fun F G j => F j + G j, fun F G j => F j - G j, fun F j => (X : R) * F j,
    fun F j => ((X⁻¹ : Rˣ) : R) * F j⟩

/-- The form with its coefficients mapped by a ring homomorphism. -/
def mapVec {S : Type} [CommRing S] (ψ : R →+* S) (F : Vec R) : Vec S :=
  fun j => ψ (F j)

theorem mapVec_isHom {S : Type} [CommRing S] (ψ : R →+* S) (X : Rˣ) :
    (vecAlgebra X).IsHom (vecAlgebra (Units.map (ψ : R →* S) X)) (mapVec ψ) where
  add F G := by
    funext j
    simp [vecAlgebra, mapVec]
  sub F G := by
    funext j
    simp [vecAlgebra, mapVec]
  mulX F := by
    funext j
    simp [vecAlgebra, mapVec]
  divX F := by
    funext j
    simp [vecAlgebra, mapVec]

theorem _root_.Rectiling.Algebra.IsHom.comp {L M N : Type} {A : Algebra L} {B : Algebra M} {C : Algebra N}
    {f : L → M} {g : M → N} (hg : B.IsHom C g) (hf : A.IsHom B f) : A.IsHom C (g ∘ f) where
  add a b := by simp [hf.add, hg.add]
  sub a b := by simp [hf.sub, hg.sub]
  mulX a := by simp [hf.mulX, hg.mulX]
  divX a := by simp [hf.divX, hg.divX]

theorem Tier.map_map {L M N : Type} (f : L → M) (g : M → N) (t : Tier L) :
    Tier.map g (Tier.map f t) = Tier.map (g ∘ f) t :=
  rfl

/-! ### Stages -/

/-- Record of an elimination: the equation, the eliminated unknown, and the previous pivot. -/
abbrev Elim (R : Type) := Vec R × ℕ × R

/-- State of the symbolic pass: the staircase, the current pivot, and the number of inside placements made. -/
structure Stage (R : Type) where
  /-- The staircase, with forms at the current stage of elimination. -/
  stairs : List (Tier (Vec R))
  /-- The current pivot. -/
  pivot : R
  /-- The number of inside placements made. -/
  count : ℕ

/-- Record of a placement, as kept along the path of the search. -/
structure Step (R : Type) where
  /-- The placement. -/
  mv : Placement
  /-- The side of the tile on which positivity is tested, at the stage of elimination current when it was placed. -/
  size : Vec R
  /-- The elimination that followed the placement, if any. -/
  elim : Option (Elim R)

/-- The free side of a tile placed inside at the given stage: the next unknown, scaled by the current pivot. -/
def Stage.side (st : Stage R) : Vec R :=
  fun j => st.pivot * unitVec (st.count + 1) j

/-- The numerators of the elimination of an unknown from a form. -/
def elimNum (E : Vec R) (m : ℕ) (F : Vec R) : Vec R :=
  fun j => E m * F j - F m * E j

open Classical in
/-- The quotient of an exact division, and zero if the division is not exact. -/
noncomputable def divExact (n d : R) : R :=
  if h : d ∣ n then h.choose else 0

theorem divExact_mul {n d : R} (h : d ∣ n) : d * divExact n d = n := by
  unfold divExact
  split
  · next h' => exact h'.choose_spec.symm
  · next h' => exact absurd h h'

/-- Every division of the elimination of an unknown from a form is exact. -/
def Divisible (e : Elim R) (F : Vec R) : Prop :=
  ∀ j, e.2.2 ∣ elimNum e.1 e.2.1 F j

/-- The form after the elimination of an unknown. -/
noncomputable def elimForm (e : Elim R) (F : Vec R) : Vec R :=
  fun j => divExact (elimNum e.1 e.2.1 F j) e.2.2

/-- The free side of the inside placement of index `j`, before any elimination. -/
def trueFresh (j : ℕ) : Vec R :=
  unitVec (j + 1)

/-- A successful symbolic pass along a path from a stage, with the records of its placements and the final equation. -/
inductive Run (X : Rˣ) : Stage R → List Placement → List (Step R) → Vec R → Prop
  | leaf {st : Stage R} {mv : Placement} {size E : Vec R}
      (hsize : positiveAt st.stairs mv st.side = some size)
      (heq : equationAt (vecAlgebra X) st.stairs mv = some E) :
      Run X st [mv] [⟨mv, size, none⟩] E
  | plain {st : Stage R} {mv : Placement} {rest : List Placement} {steps : List (Step R)}
      {size Efin : Vec R}
      (hsize : positiveAt st.stairs mv st.side = some size)
      (heq : equationAt (vecAlgebra X) st.stairs mv = none)
      (hrun : Run X ⟨place (vecAlgebra X) st.stairs mv st.side, st.pivot, nextIndex st.count mv⟩
        rest steps Efin) :
      Run X st (mv :: rest) (⟨mv, size, none⟩ :: steps) Efin
  | elim {st : Stage R} {mv : Placement} {rest : List Placement} {steps : List (Step R)}
      {size Efin E : Vec R} {m : ℕ}
      (hsize : positiveAt st.stairs mv st.side = some size)
      (heq : equationAt (vecAlgebra X) st.stairs mv = some E)
      (hm1 : 1 ≤ m) (hm : m ≤ nextIndex st.count mv) (hEm : E m ≠ 0)
      (hdiv : ∀ t ∈ place (vecAlgebra X) st.stairs mv st.side,
        Divisible (E, m, st.pivot) t.floor ∧ Divisible (E, m, st.pivot) t.wall)
      (hrun : Run X ⟨(place (vecAlgebra X) st.stairs mv st.side).map
          (Tier.map (elimForm (E, m, st.pivot))), E m, nextIndex st.count mv⟩ rest steps Efin) :
      Run X st (mv :: rest) (⟨mv, size, some (E, m, st.pivot)⟩ :: steps) Efin

/-- The eliminations recorded along a path. -/
def elims (steps : List (Step R)) : List (Elim R) :=
  steps.filterMap Step.elim

omit [CommRing R] in
@[simp]
theorem elims_nil : elims ([] : List (Step R)) = [] :=
  rfl

omit [CommRing R] in
@[simp]
theorem elims_cons_none (mv : Placement) (size : Vec R) (steps : List (Step R)) :
    elims (⟨mv, size, none⟩ :: steps) = elims steps :=
  rfl

omit [CommRing R] in
@[simp]
theorem elims_cons_some (mv : Placement) (size : Vec R) (e : Elim R) (steps : List (Step R)) :
    elims (⟨mv, size, some e⟩ :: steps) = e :: elims steps :=
  rfl

omit [CommRing R] in
theorem elims_append (a b : List (Step R)) : elims (a ++ b) = elims a ++ elims b :=
  List.filterMap_append

/-- The eliminated unknowns are sides of inside placements of the path, and the pivots do not vanish. -/
theorem Run.pivots {X : Rˣ} {st : Stage R} {path : List Placement} {steps : List (Step R)}
    {Efin : Vec R} (hrun : Run X st path steps Efin) :
    ∀ e ∈ elims steps, 1 ≤ e.2.1 ∧ e.2.1 ≤ finalIndex st.count path ∧ e.1 e.2.1 ≠ 0 := by
  induction hrun with
  | leaf => simp
  | plain _ _ _ ih =>
    intro e he
    obtain ⟨h1, h2, h3⟩ := ih e (by simpa using he)
    exact ⟨h1, h2, h3⟩
  | @elim st mv rest steps size Efin E m _ _ hm1 hm hEm _ _ ih =>
    intro e he
    rw [elims_cons_some, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨hm1, hm.trans (le_finalIndex _ _), hEm⟩
    · exact ih e he

theorem Run.length_steps {X : Rˣ} {st : Stage R} {path : List Placement} {steps : List (Step R)}
    {Efin : Vec R} (hrun : Run X st path steps Efin) : steps.length = path.length := by
  induction hrun with
  | leaf => rfl
  | plain _ _ _ ih => simp [ih]
  | elim _ _ _ _ _ _ _ ih => simp [ih]

end Forms

/-! ### Elimination over a field -/

section Carry

variable {R : Type} [CommRing R] {L : Type} [Field L]

/-- The elimination of an unknown from a form with coefficients in a field, for an elimination recorded over the ring. -/
def carryStep (ψ : R →+* L) (e : Elim R) (F : Vec L) : Vec L :=
  fun j => (ψ (e.1 e.2.1) * F j - F e.2.1 * ψ (e.1 j)) / ψ e.2.2

/-- A form carried through a sequence of eliminations. -/
def carry (ψ : R →+* L) (els : List (Elim R)) (F : Vec L) : Vec L :=
  els.foldl (fun G e => carryStep ψ e G) F

@[simp]
theorem carry_nil (ψ : R →+* L) (F : Vec L) : carry ψ [] F = F :=
  rfl

theorem carry_append (ψ : R →+* L) (a b : List (Elim R)) (F : Vec L) :
    carry ψ (a ++ b) F = carry ψ b (carry ψ a F) :=
  List.foldl_append

theorem carry_concat (ψ : R →+* L) (a : List (Elim R)) (e : Elim R) (F : Vec L) :
    carry ψ (a ++ [e]) F = carryStep ψ e (carry ψ a F) := by
  rw [carry_append]
  rfl

theorem carryStep_isHom (ψ : R →+* L) (e : Elim R) (x : Lˣ) :
    (vecAlgebra x).IsHom (vecAlgebra x) (carryStep ψ e) where
  add F G := by
    funext j
    simp only [carryStep, vecAlgebra]
    ring
  sub F G := by
    funext j
    simp only [carryStep, vecAlgebra]
    ring
  mulX F := by
    funext j
    simp only [carryStep, vecAlgebra]
    ring
  divX F := by
    funext j
    simp only [carryStep, vecAlgebra]
    ring

theorem carry_isHom (ψ : R →+* L) (els : List (Elim R)) (x : Lˣ) :
    (vecAlgebra x).IsHom (vecAlgebra x) (carry ψ els) := by
  induction els using List.reverseRecOn with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | append_singleton a e ih =>
    have h : carry ψ (a ++ [e]) = carryStep ψ e ∘ carry ψ a := by
      funext F
      exact carry_concat ψ a e F
    rw [h]
    exact (carryStep_isHom ψ e x).comp ih

/-- Over a field in which the previous pivot does not vanish, an exact elimination is the elimination over the field. -/
theorem mapVec_elimForm (ψ : R →+* L) {e : Elim R} {F : Vec R} (hπ : ψ e.2.2 ≠ 0)
    (hdiv : Divisible e F) : mapVec ψ (elimForm e F) = carryStep ψ e (mapVec ψ F) := by
  funext j
  have h := congrArg ψ (divExact_mul (hdiv j))
  simp only [elimNum, map_mul, map_sub] at h
  simp only [mapVec, elimForm, carryStep, elimNum]
  rw [eq_div_iff hπ, ← h]
  ring

/-- The eliminations seen so far, with the equations of the system that has not been reduced, and the current pivot. -/
inductive Elims (ψ : R →+* L) : List (Elim R) → List (Vec R) → R → Prop
  | nil : Elims ψ [] [] 1
  | snoc {els : List (Elim R)} {ts : List (Vec R)} {π : R} {E e : Vec R} {m : ℕ}
      (h : Elims ψ els ts π) (hπ : ψ π ≠ 0) (hE : mapVec ψ E = carry ψ els (mapVec ψ e)) :
      Elims ψ (els ++ [(E, m, π)]) (ts ++ [e]) (E m)

/-- The records of a path, related to the positivity constraints and the equations of the system that has not been reduced. -/
inductive Trace (ψ : R →+* L) :
    List (Elim R) → R → List (Step R) → List (Vec R) → List (Vec R) → Vec R → Prop
  | leaf {els : List (Elim R)} {π : R} {mv : Placement} {size p e Efin : Vec R}
      (hsize : mapVec ψ size = carry ψ els (mapVec ψ p))
      (hfin : mapVec ψ Efin = carry ψ els (mapVec ψ e)) :
      Trace ψ els π [⟨mv, size, none⟩] [p] [e] Efin
  | plain {els : List (Elim R)} {π : R} {mv : Placement} {size p Efin : Vec R}
      {steps : List (Step R)} {ps es : List (Vec R)}
      (hsize : mapVec ψ size = carry ψ els (mapVec ψ p))
      (h : Trace ψ els π steps ps es Efin) :
      Trace ψ els π (⟨mv, size, none⟩ :: steps) (p :: ps) es Efin
  | elim {els : List (Elim R)} {π : R} {mv : Placement} {size p e E Efin : Vec R} {m : ℕ}
      {steps : List (Step R)} {ps es : List (Vec R)}
      (hsize : mapVec ψ size = carry ψ els (mapVec ψ p))
      (hE : mapVec ψ E = carry ψ els (mapVec ψ e))
      (hπ : ψ π ≠ 0) (hEm : ψ (E m) ≠ 0)
      (h : Trace ψ (els ++ [(E, m, π)]) (E m) steps ps es Efin) :
      Trace ψ els π (⟨mv, size, some (E, m, π)⟩ :: steps) (p :: ps) (e :: es) Efin

variable (ψ : R →+* L) (X : Rˣ)

/-- One placement on the staircase at a stage of elimination and on the staircase that has not been reduced. -/
theorem step_link {st : Stage R} {els : List (Elim R)} {sT : List (Tier (Vec R))}
    (hst : st.stairs.map (Tier.map (mapVec ψ)) =
      sT.map (Tier.map fun F => carry ψ els (mapVec ψ F)))
    (hfresh : ∀ u, st.count < u → carry ψ els (mapVec ψ (unitVec u)) =
      fun j => ψ st.pivot * mapVec ψ (unitVec u) j) (mv : Placement) :
    (place (vecAlgebra X) st.stairs mv st.side).map (Tier.map (mapVec ψ)) =
        (place (vecAlgebra X) sT mv (trueFresh st.count)).map
          (Tier.map fun F => carry ψ els (mapVec ψ F)) ∧
      (positiveAt st.stairs mv st.side).map (mapVec ψ) =
        (positiveAt sT mv (trueFresh st.count)).map (fun F => carry ψ els (mapVec ψ F)) ∧
      (equationAt (vecAlgebra X) st.stairs mv).map (mapVec ψ) =
        (equationAt (vecAlgebra X) sT mv).map (fun F => carry ψ els (mapVec ψ F)) := by
  have hom1 := mapVec_isHom ψ X
  have hom2 : (vecAlgebra X).IsHom (vecAlgebra (Units.map (ψ : R →* L) X))
      (fun F => carry ψ els (mapVec ψ F)) :=
    (carry_isHom ψ els _).comp hom1
  have hside : mapVec ψ st.side = carry ψ els (mapVec ψ (trueFresh st.count)) := by
    rw [trueFresh, hfresh _ (Nat.lt_succ_self _)]
    funext j
    simp [mapVec, Stage.side]
  refine ⟨?_, ?_, ?_⟩
  · rw [place_map hom1, hst, hside, ← place_map hom2]
  · rw [← positiveAt_map (f := mapVec ψ), hst, hside,
      positiveAt_map (f := fun F => carry ψ els (mapVec ψ F))]
  · rw [← equationAt_map hom1, hst, equationAt_map hom2]

/-- The records of a successful symbolic pass are related to the system that has not been reduced, over any field in which no pivot vanishes. -/
theorem Run.trace {st : Stage R} {path : List Placement} {steps : List (Step R)} {Efin : Vec R}
    (hrun : Run X st path steps Efin) :
    ∀ (els : List (Elim R)) (sT : List (Tier (Vec R))),
      (∀ e ∈ elims steps, ψ (e.1 e.2.1) ≠ 0) → ψ st.pivot ≠ 0 →
      st.stairs.map (Tier.map (mapVec ψ)) = sT.map (Tier.map fun F => carry ψ els (mapVec ψ F)) →
      (∀ u, st.count < u → carry ψ els (mapVec ψ (unitVec u)) =
        fun j => ψ st.pivot * mapVec ψ (unitVec u) j) →
      Trace ψ els st.pivot steps (positives (vecAlgebra X) trueFresh sT st.count path)
        (equations (vecAlgebra X) trueFresh sT st.count path) Efin := by
  induction hrun with
  | @leaf st mv size E hsize heq =>
    intro els sT _ _ hst hfresh
    obtain ⟨-, hpos, hequ⟩ := step_link ψ X hst hfresh mv
    rw [hsize] at hpos
    rw [heq] at hequ
    obtain ⟨p, hp, hp'⟩ := Option.map_eq_some_iff.mp hpos.symm
    obtain ⟨e, he, he'⟩ := Option.map_eq_some_iff.mp hequ.symm
    simp only [positives, equations, hp, he, Option.toList_some, List.append_nil]
    exact Trace.leaf hp'.symm he'.symm
  | @plain st mv rest steps size Efin hsize heq _ ih =>
    intro els sT hpiv hπ hst hfresh
    obtain ⟨hnext, hpos, hequ⟩ := step_link ψ X hst hfresh mv
    rw [hsize] at hpos
    rw [heq] at hequ
    obtain ⟨p, hp, hp'⟩ := Option.map_eq_some_iff.mp hpos.symm
    have he : equationAt (vecAlgebra X) sT mv (L := Vec R) = none := by
      simpa using hequ.symm
    simp only [positives, equations, hp, he, Option.toList_some, Option.toList_none,
      List.nil_append, List.singleton_append]
    refine Trace.plain hp'.symm (ih els _ hpiv hπ hnext fun u hu => hfresh u ?_)
    exact lt_of_le_of_lt (le_nextIndex _ _) hu
  | @elim st mv rest steps size Efin E m hsize heq hm1 hm hEm hdiv _ ih =>
    intro els sT hpiv hπ hst hfresh
    obtain ⟨hnext, hpos, hequ⟩ := step_link ψ X hst hfresh mv
    rw [hsize] at hpos
    rw [heq] at hequ
    obtain ⟨p, hp, hp'⟩ := Option.map_eq_some_iff.mp hpos.symm
    obtain ⟨e, he, he'⟩ := Option.map_eq_some_iff.mp hequ.symm
    simp only [positives, equations, hp, he, Option.toList_some, List.singleton_append]
    have hEm' : ψ (E m) ≠ 0 := hpiv (E, m, st.pivot) (by simp)
    refine Trace.elim hp'.symm he'.symm hπ hEm' (ih (els ++ [(E, m, st.pivot)]) _
      (fun e he => hpiv e (by simp [he])) hEm' ?_ ?_)
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
      rw [carry_concat, hfresh u (lt_of_le_of_lt (le_nextIndex _ _) hu)]
      funext j
      have hu' : nextIndex st.count mv < u := hu
      have hmu : m ≠ u := by omega
      simp only [carryStep, mapVec, unitVec, hmu, ite_false, map_zero, mul_zero, zero_mul,
        sub_zero]
      field_simp

end Carry

end Fast

end Rectiling
