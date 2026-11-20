-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Determinant

/-!
# The reduced system of a complete path

The homogeneous system of a placement sequence, for a main rectangle of sides `a t` and `b t` in the scale `t`, and what the symbolic pass along a complete path says about its real solutions.

- The final equation has the determinant of the system as its scale coefficient, up to sign (`Run.final_eq_det`), so the coefficient vanishes wherever the system has a solution of scale one (`Run.final_vanishes`).
- Where no pivot vanishes, back-substitution gives the only candidate solution of scale one (`Run.solution`).
-/

namespace Rectiling

namespace Fast

/-! ### Complete sequences and scaling -/

/-- A complete admissible sequence obeys the rules on stale tiers and started floors, whatever the lengths. -/
theorem allowed_of_complete {L : Type} (A : Algebra L) (fresh : ℕ → L) (w h : L) {n : ℕ}
    {path : List Placement} (hpath : Complete n path) : Allowed A fresh (initial w h) 0 path := by
  have aux : ∀ (path : List Placement) (s : List (Tier Unit)) (n k : ℕ),
      CompleteFrom s n path → Allowed unitAlgebra (fun _ => ()) s k path := by
    intro path
    induction path with
    | nil => intro s n k h; exact h
    | cons mv rest ih => intro s n k h; exact ⟨h.1.1, ih _ _ _ h.2⟩
  exact (allowed_map (Algebra.isHom_unit A) fresh (initial w h) 0 path).mp (aux path _ n 0 hpath)

/-- The constraints over the reals are invariant under a change of scale. -/
theorem satisfies_scale {x c : ℝ} (hc : 0 < c) (fresh : ℕ → ℝ) (s : List (Tier ℝ)) (k : ℕ)
    (path : List Placement) :
    Satisfies x (fun j => c * fresh j) (s.map (Tier.map fun l => c * l)) k path ↔
      Satisfies x fresh s k path := by
  have hom : (realAlgebra x).IsHom (realAlgebra x) fun l => c * l :=
    ⟨fun a b => by simp only [realAlgebra]; ring, fun a b => by simp only [realAlgebra]; ring,
      fun a => by simp only [realAlgebra]; ring, fun a => by simp only [realAlgebra]; ring⟩
  have hpos := positives_map hom fresh s k path
  have heq := equations_map hom fresh s k path
  change positives _ (fun j => c * fresh j) _ _ _ = _ at hpos
  change equations _ (fun j => c * fresh j) _ _ _ = _ at heq
  unfold Satisfies
  rw [hpos, heq]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    mul_pos_iff_of_pos_left hc, mul_eq_zero, hc.ne', false_or]

section Hom

variable {R : Type} [CommRing R]

/-- The staircase of the empty main rectangle, whose sides are multiples of the scale. -/
def homInitial (a b : ℤ) : List (Tier (Vec R)) :=
  initial (fun j => (a : R) * unitVec 0 j) (fun j => (b : R) * unitVec 0 j)

/-- The stage at which the symbolic pass starts. -/
def Stage.init (a b : ℤ) : Stage R :=
  ⟨homInitial a b, 1, 0⟩

/-- The equations of the homogeneous system of a placement sequence. -/
def homEquations (X : Rˣ) (a b : ℤ) (path : List Placement) : List (Vec R) :=
  equations (vecAlgebra X) trueFresh (homInitial a b) 0 path

/-- The positivity constraints of the homogeneous system of a placement sequence. -/
def homPositives (X : Rˣ) (a b : ℤ) (path : List Placement) : List (Vec R) :=
  positives (vecAlgebra X) trueFresh (homInitial a b) 0 path

theorem length_homEquations (X : Rˣ) (a b : ℤ) {n : ℕ} {path : List Placement}
    (hpath : Complete n path) : (homEquations X a b path).length = finalIndex 0 path + 1 := by
  have := length_equations (vecAlgebra X) trueFresh path (homInitial a b) 0
    (allowed_of_complete _ _ _ _ hpath)
  simp only [homInitial, initial, List.length_cons, List.length_nil, add_zero] at this
  unfold homEquations homInitial initial
  omega

variable (φ : R →+* ℝ)

/-- The value of a form at a real assignment of the unknowns of index below `N`. -/
noncomputable def val (N : ℕ) (v : ℕ → ℝ) (F : Vec R) : ℝ :=
  dot N (mapVec φ F) v

theorem val_isHom (X : Rˣ) (N : ℕ) (v : ℕ → ℝ) :
    (vecAlgebra X).IsHom (realAlgebra (φ X)) (val φ N v) where
  add F G := by
    simp only [val, dot, mapVec, vecAlgebra, realAlgebra, map_add, add_mul,
      Finset.sum_add_distrib]
  sub F G := by
    simp only [val, dot, mapVec, vecAlgebra, realAlgebra, map_sub, sub_mul,
      Finset.sum_sub_distrib]
  mulX F := by
    simp only [val, dot, mapVec, vecAlgebra, realAlgebra, map_mul, mul_assoc, Finset.mul_sum]
  divX F := by
    simp only [val, dot, mapVec, vecAlgebra, realAlgebra, map_mul, map_units_inv, mul_assoc,
      div_eq_inv_mul, Finset.mul_sum]

theorem val_scale (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ) (z : ℤ) :
    val φ N v (fun j => (z : R) * unitVec 0 j) = z * v 0 := by
  unfold val dot
  rw [Finset.sum_eq_single 0]
  · simp [mapVec, unitVec]
  · intro j _ hj
    simp [mapVec, unitVec, hj]
  · intro h
    exact absurd (Finset.mem_range.mpr hN) h

theorem val_unitVec (N : ℕ) (v : ℕ → ℝ) {u : ℕ} (hu : u < N) : val φ N v (unitVec u) = v u := by
  unfold val dot
  rw [Finset.sum_eq_single u]
  · simp [mapVec, unitVec]
  · intro j _ hj
    simp [mapVec, unitVec, hj]
  · intro h
    exact absurd (Finset.mem_range.mpr hu) h

/-- The constraints over the reals, for a main rectangle of sides `a` and `b`, hold exactly when the homogeneous system holds at the assignment of scale one. -/
theorem satisfies_iff_hom (X : Rˣ) (a b : ℤ) (path : List Placement) (v : ℕ → ℝ) (hv : v 0 = 1) :
    Satisfies (φ X) (fun j => v (j + 1)) (initial (a : ℝ) (b : ℝ)) 0 path ↔
      (∀ p ∈ homPositives X a b path, 0 < val φ (finalIndex 0 path + 1) v p) ∧
        ∀ e ∈ homEquations X a b path, val φ (finalIndex 0 path + 1) v e = 0 := by
  have hom := val_isHom φ X (finalIndex 0 path + 1) v
  have hinit : (homInitial a b).map (Tier.map (val φ (finalIndex 0 path + 1) v)) =
      initial (a : ℝ) (b : ℝ) := by
    simp [homInitial, initial, Tier.map, val_scale, hv]
  have hcongr := run_congr (realAlgebra (φ X))
    (f := val φ (finalIndex 0 path + 1) v ∘ trueFresh) (g := fun j => v (j + 1)) path
    (initial (a : ℝ) (b : ℝ)) 0 (by
      intro j _ hj
      simp only [Function.comp_apply, trueFresh]
      exact val_unitVec φ _ v (by omega))
  have hpos := positives_map hom trueFresh (homInitial a b) 0 path
  have heq := equations_map hom trueFresh (homInitial a b) 0 path
  rw [hinit, hcongr.2.1] at hpos
  rw [hinit, hcongr.2.2] at heq
  unfold Satisfies homPositives homEquations
  rw [hpos, heq]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- The assignment of scale one obtained by back-substitution through the equations recorded along a path. -/
noncomputable def solutionOf (path : List Placement) (steps : List (Step R)) : ℕ → ℝ :=
  back φ (finalIndex 0 path + 1) (elims steps) fun j => if j = 0 then 1 else 0

/-- **The candidate solution.** Along a complete path on which the symbolic pass succeeds, at a real point where no pivot vanishes: back-substitution yields an assignment of scale one; if the final equation involves the scale only, the assignment solves the homogeneous system exactly when the scale coefficient of the final equation vanishes; every solution of scale one coincides with it; and the size recorded for each placement, carried through the later eliminations, takes on it the value of the positivity constraint multiplied by the last pivot, which does not vanish. -/
theorem Run.solution {X : Rˣ} {a b : ℤ} {n : ℕ} {path : List Placement} {steps : List (Step R)}
    {Efin : Vec R} (hpath : Complete n path) (hrun : Run X (Stage.init a b) path steps Efin)
    (hpiv : ∀ e ∈ elims steps, φ (e.1 e.2.1) ≠ 0) :
    solutionOf φ path steps 0 = 1 ∧
      ((∀ j, 0 < j → φ (Efin j) = 0) →
        ((∀ e ∈ homEquations X a b path,
          val φ (finalIndex 0 path + 1) (solutionOf φ path steps) e = 0) ↔ φ (Efin 0) = 0)) ∧
      (∀ w : ℕ → ℝ, w 0 = 1 →
        (∀ e ∈ homEquations X a b path, val φ (finalIndex 0 path + 1) w e = 0) →
        ∀ j < finalIndex 0 path + 1, w j = solutionOf φ path steps j) ∧
      ∃ πf : R, φ πf ≠ 0 ∧ ∀ (q : ℕ) (s : Step R), steps[q]? = some s →
        ∃ p, (homPositives X a b path)[q]? = some p ∧
          dot (finalIndex 0 path + 1) (carry φ (elims (steps.drop q)) (mapVec φ s.size))
            (solutionOf φ path steps) =
            φ πf * val φ (finalIndex 0 path + 1) (solutionOf φ path steps) p := by
  set N := finalIndex 0 path + 1 with hN
  set v := solutionOf φ path steps with hvdef
  have h1 : φ 1 ≠ 0 := by simp
  have htr : Trace φ [] 1 steps (homPositives X a b path) (homEquations X a b path) Efin :=
    hrun.trace φ X [] (homInitial a b) hpiv h1 rfl (by
      intro u _
      funext j
      simp [Stage.init])
  obtain ⟨esI, e, πf, hes, hEl, hπf, hfin⟩ := htr.elims [] Elims.nil h1
  simp only [List.nil_append] at hEl hfin
  have hlen : (elims steps).length = finalIndex 0 path := by
    have h2 := length_homEquations X a b hpath
    rw [hes, List.length_append, List.length_singleton] at h2
    rw [hEl.length_eq]
    omega
  have hpv : ∀ e ∈ elims steps, 1 ≤ e.2.1 ∧ e.2.1 ≤ finalIndex 0 path ∧ e.1 e.2.1 ≠ 0 :=
    hrun.pivots
  have hpw := hEl.pairwise
  have hmN : ∀ e ∈ elims steps, e.2.1 < N := fun e he => by
    have := (hpv e he).2.1
    omega
  have hm0 : ∀ e ∈ elims steps, e.2.1 ≠ 0 := fun e he => by
    have := (hpv e he).1
    omega
  have hv0 : v 0 = 1 := by
    rw [hvdef, solutionOf, back_of_not_mem φ _ _ _ hm0]
    simp
  have hstage : ∀ e ∈ elims steps, dot N (mapVec φ e.1) v = 0 :=
    back_solves φ hpw hmN hpiv _
  have htrue : ∀ t ∈ esI, dot N (mapVec φ t) v = 0 := hEl.true_of_stage hstage
  refine ⟨hv0, ?_, ?_, πf, hπf, ?_⟩
  · intro hz
    have hdot : dot N (mapVec φ Efin) v = φ (Efin 0) := by
      unfold dot
      rw [Finset.sum_eq_single 0]
      · simp [mapVec, hv0]
      · intro j _ hj
        simp [mapVec, hz j (Nat.pos_of_ne_zero hj)]
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
    have hcar := hEl.dot_carry htrue (mapVec φ e)
    rw [← hfin, hdot] at hcar
    rw [hes]
    constructor
    · intro hall
      have he : val φ N v e = 0 := hall e (by simp)
      rw [hcar]
      unfold val at he
      rw [he, mul_zero]
    · intro hzero t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact htrue t ht
      · obtain rfl : t = e := by simpa using ht
        rw [hzero] at hcar
        exact (mul_eq_zero.mp hcar.symm).resolve_left hπf
  · intro w hw0 hw j hj
    have hwI : ∀ t ∈ esI, dot N (mapVec φ t) w = 0 := fun t ht => hw t (by rw [hes]; simp [ht])
    have hwstage := hEl.stage_of_true hwI
    have hcov : ∀ j < N, j = 0 ∨ (∃ e ∈ ([] : List (Elim R)), e.2.1 = j) ∨
        ∃ e ∈ elims steps, e.2.1 = j := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (covers (nodup_pivots φ hpw hpiv)
          (fun e he => ⟨(hpv e he).1, (hpv e he).2.1⟩) hlen h (by omega)))
    have huniq := back_unique φ (N := N) (v0 := fun j => if j = 0 then 1 else 0) (w := w)
      (by simp [hw0]) (elims steps) [] (by simpa using hpw) hmN hpiv hm0 hcov hwstage
    rcases hcov j hj with h | ⟨e', he', -⟩ | ⟨e', he', h⟩
    · rw [h, hw0, hv0]
    · simp at he'
    · rw [← h]
      exact (huniq e' he').symm
  · intro q s hs
    obtain ⟨p, hp, hsize⟩ := htr.size.2 q s hs
    refine ⟨p, hp, ?_⟩
    rw [hsize, List.nil_append, ← carry_append, ← elims_append, List.take_append_drop]
    exact hEl.dot_carry htrue (mapVec φ p)

/-- Where no pivot vanishes, no previous pivot does. -/
theorem Run.prev_ne_zero {X : Rˣ} {a b : ℤ} {path : List Placement} {steps : List (Step R)}
    {Efin : Vec R} (hrun : Run X (Stage.init a b) path steps Efin)
    (hpiv : ∀ e ∈ elims steps, φ (e.1 e.2.1) ≠ 0) : ∀ e ∈ elims steps, φ e.2.2 ≠ 0 := by
  have h1 : φ 1 ≠ 0 := by simp
  have htr : Trace φ [] 1 steps (homPositives X a b path) (homEquations X a b path) Efin :=
    hrun.trace φ X [] (homInitial a b) hpiv h1 rfl (by
      intro u _
      funext j
      simp [Stage.init])
  obtain ⟨esI, e, πf, -, hEl, -, -⟩ := htr.elims [] Elims.nil h1
  simp only [List.nil_append] at hEl
  exact hEl.prev_ne_zero

/-- The positivity constraints over the reals are the values of those of the homogeneous system. -/
theorem positives_hom (X : Rˣ) (a b : ℤ) (path : List Placement) (v : ℕ → ℝ) (hv : v 0 = 1) :
    positives (realAlgebra (φ X)) (fun j => v (j + 1)) (initial (a : ℝ) (b : ℝ)) 0 path =
      (homPositives X a b path).map (val φ (finalIndex 0 path + 1) v) := by
  have hom := val_isHom φ X (finalIndex 0 path + 1) v
  have hinit : (homInitial a b).map (Tier.map (val φ (finalIndex 0 path + 1) v)) =
      initial (a : ℝ) (b : ℝ) := by
    simp [homInitial, initial, Tier.map, val_scale, hv]
  have hcongr := run_congr (realAlgebra (φ X))
    (f := val φ (finalIndex 0 path + 1) v ∘ trueFresh) (g := fun j => v (j + 1)) path
    (initial (a : ℝ) (b : ℝ)) 0 (by
      intro j _ hj
      simp only [Function.comp_apply, trueFresh]
      exact val_unitVec φ _ v (by omega))
  have hpos := positives_map hom trueFresh (homInitial a b) 0 path
  rw [hinit, hcongr.2.1] at hpos
  exact hpos

/-- The equations over the reals are the values of those of the homogeneous system. -/
theorem equations_hom (X : Rˣ) (a b : ℤ) (path : List Placement) (v : ℕ → ℝ) (hv : v 0 = 1) :
    equations (realAlgebra (φ X)) (fun j => v (j + 1)) (initial (a : ℝ) (b : ℝ)) 0 path =
      (homEquations X a b path).map (val φ (finalIndex 0 path + 1) v) := by
  have hom := val_isHom φ X (finalIndex 0 path + 1) v
  have hinit : (homInitial a b).map (Tier.map (val φ (finalIndex 0 path + 1) v)) =
      initial (a : ℝ) (b : ℝ) := by
    simp [homInitial, initial, Tier.map, val_scale, hv]
  have hcongr := run_congr (realAlgebra (φ X))
    (f := val φ (finalIndex 0 path + 1) v ∘ trueFresh) (g := fun j => v (j + 1)) path
    (initial (a : ℝ) (b : ℝ)) 0 (by
      intro j _ hj
      simp only [Function.comp_apply, trueFresh]
      exact val_unitVec φ _ v (by omega))
  have heq := equations_map hom trueFresh (homInitial a b) 0 path
  rw [hinit, hcongr.2.2] at heq
  exact heq

theorem val_congr (N : ℕ) {v w : ℕ → ℝ} (h : ∀ j < N, w j = v j) (F : Vec R) :
    val φ N w F = val φ N v F := by
  unfold val dot
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

end Hom

/-! ### The determinant -/

section Det

variable {R : Type} [CommRing R] [IsDomain R]

theorem det_congr_size {S : Type} [CommRing S] (f : ℕ → ℕ → S) {n n' : ℕ} (h : n = n') :
    (Matrix.of fun i j : Fin n => f i j).det = (Matrix.of fun i j : Fin n' => f i j).det := by
  subst h
  rfl

/-- **The proportion polynomial is the determinant.** Along a complete path on which the symbolic pass succeeds, the scale coefficient of the final equation is, up to sign, the determinant of the homogeneous system. -/
theorem Run.final_eq_det {X : Rˣ} {a b : ℤ} {n : ℕ} {path : List Placement}
    {steps : List (Step R)} {Efin : Vec R} (hpath : Complete n path)
    (hrun : Run X (Stage.init a b) path steps Efin) :
    ∃ s : ℤˣ, Efin 0 = ((s : ℤ) : R) *
      (Matrix.of fun i j : Fin (finalIndex 0 path + 1) =>
        (homEquations X a b path).getD i 0 j).det := by
  let ψ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hinj : Function.Injective ψ := IsFractionRing.injective R (FractionRing R)
  have hpv : ∀ e ∈ elims steps, 1 ≤ e.2.1 ∧ e.2.1 ≤ finalIndex 0 path ∧ e.1 e.2.1 ≠ 0 :=
    hrun.pivots
  have hpiv : ∀ e ∈ elims steps, ψ (e.1 e.2.1) ≠ 0 := fun e he =>
    (map_ne_zero_iff ψ hinj).mpr (hpv e he).2.2
  have h1 : ψ 1 ≠ 0 := by simp
  have htr : Trace ψ [] 1 steps (homPositives X a b path) (homEquations X a b path) Efin :=
    hrun.trace ψ X [] (homInitial a b) hpiv h1 rfl (by
      intro u _
      funext j
      simp [Stage.init])
  obtain ⟨esI, e, πf, hes, hEl, hπf, hfin⟩ := htr.elims [] Elims.nil h1
  simp only [List.nil_append] at hEl hfin
  have hlen : (elims steps).length = finalIndex 0 path := by
    have h2 := length_homEquations X a b hpath
    rw [hes, List.length_append, List.length_singleton] at h2
    rw [hEl.length_eq]
    omega
  have hEl' : Elims ψ (elims steps ++ [(Efin, 0, πf)]) (esI ++ [e]) (Efin 0) :=
    hEl.snoc hπf hfin
  have hlen' : (elims steps ++ [(Efin, 0, πf)]).length = finalIndex 0 path + 1 := by
    simp [hlen]
  have hm : ∀ e ∈ elims steps ++ [(Efin, 0, πf)],
      e.2.1 < (elims steps ++ [(Efin, 0, πf)]).length := by
    intro e' he'
    rw [hlen']
    rcases List.mem_append.mp he' with he' | he'
    · have := (hpv e' he').2.1
      omega
    · obtain rfl : e' = (Efin, 0, πf) := by simpa using he'
      exact Nat.succ_pos _
  have hnd : ((elims steps ++ [(Efin, 0, πf)]).map fun e : Elim R => e.2.1).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨nodup_pivots ψ hEl.pairwise hpiv, by simp, ?_⟩
    intro i hi j hj
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hi
    have := (hpv e' he').1
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hj
    omega
  obtain ⟨s, hs⟩ := hEl'.det_eq hm hnd
  refine ⟨s, hinj ?_⟩
  rw [hs, det_congr_size (fun i j => ψ ((esI ++ [e]).getD i 0 j)) hlen', map_mul, map_intCast,
    RingHom.map_det, ← hes]
  rfl

/-- **The proportion polynomial vanishes at every solution.** If the homogeneous system of a complete path has a real solution of scale one, the scale coefficient of the final equation vanishes there, whether or not a pivot does. -/
theorem Run.final_vanishes (φ : R →+* ℝ) {X : Rˣ} {a b : ℤ} {n : ℕ} {path : List Placement}
    {steps : List (Step R)} {Efin : Vec R} (hpath : Complete n path)
    (hrun : Run X (Stage.init a b) path steps Efin) {w : ℕ → ℝ} (hw0 : w 0 = 1)
    (hw : ∀ e ∈ homEquations X a b path, val φ (finalIndex 0 path + 1) w e = 0) :
    φ (Efin 0) = 0 := by
  obtain ⟨s, hs⟩ := hrun.final_eq_det hpath
  have hlen := length_homEquations X a b hpath
  rw [hs, map_mul, RingHom.map_det]
  have hdet : (φ.mapMatrix (Matrix.of fun i j : Fin (finalIndex 0 path + 1) =>
      (homEquations X a b path).getD i 0 j)).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun j => w j, ?_, ?_⟩
    · intro h
      have := congrFun h ⟨0, Nat.succ_pos _⟩
      simp [hw0] at this
    · funext i
      have hi : (i : ℕ) < (homEquations X a b path).length := by
        rw [hlen]
        exact i.isLt
      have hmem : (homEquations X a b path).getD i 0 ∈ homEquations X a b path := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem _
      have := hw _ hmem
      unfold val dot at this
      simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply]
      rw [Fin.sum_univ_eq_sum_range
        (fun j => φ ((homEquations X a b path).getD i 0 j) * w j) (finalIndex 0 path + 1)]
      exact this
  rw [hdet, mul_zero]

end Det

end Fast

end Rectiling
