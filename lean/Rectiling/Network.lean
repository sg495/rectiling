-- SPDX-License-Identifier: LGPL-3.0-or-later
import Mathlib

/-!
# Networks, flows and impedance

Electrical networks with two poles, flows for real resistances, the linear system of Ohm's and Kirchhoff's laws as a square matrix over any commutative ring, and the impedance of a network with positive resistances.
-/

namespace Rectiling

/-- Graph with multiple edges, each with a reference direction from its tail to its head, and two poles. -/
structure Network (V E : Type*) where
  /-- Tail of an edge. -/
  tail : E → V
  /-- Head of an edge. -/
  head : E → V
  /-- The pole at which the current enters. -/
  source : V
  /-- The pole at which the current leaves. -/
  sink : V

namespace Network

variable {V E : Type*}

/-- Two vertices joined by an edge, in either direction. -/
def Adj (N : Network V E) (a b : V) : Prop :=
  ∃ e, (N.tail e = a ∧ N.head e = b) ∨ (N.tail e = b ∧ N.head e = a)

/-- The poles are distinct, no edge is a loop, and the graph is connected. -/
structure Proper (N : Network V E) : Prop where
  /-- The poles are distinct. -/
  source_ne_sink : N.source ≠ N.sink
  /-- No edge is a loop. -/
  loopless : ∀ e, N.tail e ≠ N.head e
  /-- Every vertex is joined to the sink by a path. -/
  connected : ∀ v, Relation.ReflTransGen N.Adj v N.sink

/-- A function that takes equal values at the two ends of every edge of a connected network is constant. -/
theorem Proper.eq_sink {N : Network V E} (hN : N.Proper) {R : Type*} (f : V → R)
    (hf : ∀ e, f (N.tail e) = f (N.head e)) (v : V) : f v = f N.sink := by
  refine Relation.ReflTransGen.head_induction_on (motive := fun a _ => f a = f N.sink) (hN.connected v) rfl ?_
  rintro a c ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ _ ih
  · rw [hf e, ih]
  · rw [← hf e, ih]

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] {R : Type*} [CommRing R]

/-- Net current leaving a vertex. -/
def div (N : Network V E) (i : E → R) (v : V) : R :=
  ∑ e, ((if N.tail e = v then i e else 0) - (if N.head e = v then i e else 0))

omit [DecidableEq E] in
/-- Summation by parts: the potentials weighted by the net currents sum to the potential differences weighted by the currents. -/
theorem sum_mul_div (N : Network V E) (φ : V → R) (i : E → R) :
    ∑ v, φ v * N.div i v = ∑ e, (φ (N.tail e) - φ (N.head e)) * i e := by
  simp only [div, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  ring

omit [DecidableEq E] in
/-- The net currents of all vertices sum to zero. -/
theorem sum_div (N : Network V E) (i : E → R) : ∑ v, N.div i v = 0 := by
  have h := N.sum_mul_div (fun _ => (1 : R)) i
  simpa using h

omit [Fintype V] [DecidableEq E] in
theorem div_sub (N : Network V E) (i j : E → R) (v : V) : N.div (i - j) v = N.div i v - N.div j v := by
  simp only [div, ← Finset.sum_sub_distrib, Pi.sub_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

omit [Fintype V] [DecidableEq E] in
theorem div_smul (N : Network V E) (k : R) (i : E → R) (v : V) : N.div (k • i) v = k * N.div i v := by
  simp only [div, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

omit [DecidableEq E] in
/-- Kirchhoff's law at the sink follows from the law at the other vertices. -/
theorem div_eq_of_ne_sink (N : Network V E) (hst : N.source ≠ N.sink) {i : E → R} {J : R}
    (h : ∀ v, v ≠ N.sink → N.div i v = if v = N.source then J else 0) (v : V) :
    N.div i v = J * ((if v = N.source then 1 else 0) - (if v = N.sink then 1 else 0)) := by
  by_cases hv : v = N.sink
  · subst hv
    have h0 := N.sum_div i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ N.sink)] at h0
    have h1 : ∑ v ∈ Finset.univ.erase N.sink, N.div i v = J := by
      rw [Finset.sum_congr rfl fun v hv => h v (Finset.ne_of_mem_erase hv)]
      simp [hst]
    rw [h1] at h0
    simp only [Ne.symm hst, ↓reduceIte]
    linear_combination h0
  · simp only [h v hv, hv, ↓reduceIte]
    split_ifs <;> ring

/-- Flow of value `I` for the resistances `r`: a potential and a current that satisfy Ohm's law on every edge and Kirchhoff's law at every vertex. -/
structure IsFlow (N : Network V E) (r : E → ℝ) (I : ℝ) (φ : V → ℝ) (i : E → ℝ) : Prop where
  /-- Ohm's law. -/
  ohm : ∀ e, φ (N.tail e) - φ (N.head e) = r e * i e
  /-- Kirchhoff's law. -/
  kirchhoff : ∀ v, N.div i v = I * ((if v = N.source then 1 else 0) - (if v = N.sink then 1 else 0))

namespace IsFlow

variable {N : Network V E} {r : E → ℝ} {I I' : ℝ} {φ φ' : V → ℝ} {i i' : E → ℝ}

omit [DecidableEq E] in
/-- The power dissipated in the edges is the value multiplied by the potential difference between the poles. -/
theorem energy (h : N.IsFlow r I φ i) : ∑ e, r e * i e ^ 2 = I * (φ N.source - φ N.sink) := by
  have h0 := N.sum_mul_div φ i
  simp only [h.kirchhoff, h.ohm] at h0
  have h1 : ∑ v, φ v * (I * ((if v = N.source then 1 else 0) - (if v = N.sink then 1 else 0))) =
      I * (φ N.source - φ N.sink) := by
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  rw [← h1, h0]
  exact Finset.sum_congr rfl fun e _ => by ring

omit [Fintype V] [DecidableEq E] in
theorem sub (h : N.IsFlow r I φ i) (h' : N.IsFlow r I' φ' i') : N.IsFlow r (I - I') (φ - φ') (i - i') where
  ohm e := by
    simp only [Pi.sub_apply, mul_sub]
    linarith [h.ohm e, h'.ohm e]
  kirchhoff v := by
    rw [div_sub, h.kirchhoff, h'.kirchhoff]
    ring

omit [Fintype V] [DecidableEq E] in
theorem smul (k : ℝ) (h : N.IsFlow r I φ i) : N.IsFlow r (k * I) (k • φ) (k • i) where
  ohm e := by
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination k * h.ohm e
  kirchhoff v := by
    rw [div_smul, h.kirchhoff]
    ring

omit [Fintype V] [DecidableEq E] in
/-- A flow in which no edge dissipates power has no current and a constant potential. -/
theorem trivial_of_forall (hN : N.Proper) (h : N.IsFlow r I φ i) (hr : ∀ e, r e ≠ 0)
    (h0 : ∀ e, r e * i e ^ 2 = 0) : i = 0 ∧ ∀ v, φ v = φ N.sink := by
  have hi : ∀ e, i e = 0 := fun e => by
    rcases mul_eq_zero.mp (h0 e) with h1 | h1
    · exact absurd h1 (hr e)
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
  refine ⟨funext hi, hN.eq_sink φ fun e => ?_⟩
  have := h.ohm e
  rw [hi e, mul_zero] at this
  linarith

omit [DecidableEq E] in
/-- A flow for positive resistances whose value and potential difference have a product that is not positive is trivial. -/
theorem trivial_of_pos (hN : N.Proper) (h : N.IsFlow r I φ i) (hr : ∀ e, 0 < r e)
    (hI : I * (φ N.source - φ N.sink) ≤ 0) : i = 0 ∧ ∀ v, φ v = φ N.sink := by
  refine h.trivial_of_forall hN (fun e => (hr e).ne') ?_
  have hnn : ∀ e ∈ Finset.univ, 0 ≤ r e * i e ^ 2 := fun e _ => mul_nonneg (hr e).le (sq_nonneg _)
  have hs : ∑ e, r e * i e ^ 2 = 0 :=
    le_antisymm (h.energy ▸ hI) (Finset.sum_nonneg hnn)
  exact fun e => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs e (Finset.mem_univ e)

omit [DecidableEq E] in
/-- A flow for negative resistances whose value and potential difference have a product that is not negative is trivial. -/
theorem trivial_of_neg (hN : N.Proper) (h : N.IsFlow r I φ i) (hr : ∀ e, r e < 0)
    (hI : 0 ≤ I * (φ N.source - φ N.sink)) : i = 0 ∧ ∀ v, φ v = φ N.sink := by
  refine h.trivial_of_forall hN (fun e => (hr e).ne) ?_
  have hnp : ∀ e ∈ Finset.univ, r e * i e ^ 2 ≤ 0 := fun e _ =>
    mul_nonpos_of_nonpos_of_nonneg (hr e).le (sq_nonneg _)
  have hs : ∑ e, r e * i e ^ 2 = 0 :=
    le_antisymm (Finset.sum_nonpos hnp) (h.energy ▸ hI)
  exact fun e => (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hs e (Finset.mem_univ e)

omit [DecidableEq E] in
/-- Two flows of the same value for positive resistances have the same current, and their potentials differ by a constant. -/
theorem unique (hN : N.Proper) (hr : ∀ e, 0 < r e) (h : N.IsFlow r I φ i) (h' : N.IsFlow r I φ' i') :
    i = i' ∧ ∀ v, φ v - φ' v = φ N.sink - φ' N.sink := by
  have hd := h.sub h'
  rw [sub_self] at hd
  obtain ⟨h1, h2⟩ := hd.trivial_of_pos hN hr (by rw [zero_mul])
  exact ⟨sub_eq_zero.mp h1, fun v => h2 v⟩

end IsFlow

/-- The square matrix of the linear system in the currents and the potentials: for each edge `e` the equation `a e * (φ (tail e) - φ (head e)) = b e * i e`, for each vertex other than the sink the net current, less `c * φ source` at the source, and for the sink its potential. -/
def system (N : Network V E) (a b : E → R) (c : R) : Matrix (E ⊕ V) (E ⊕ V) R :=
  Matrix.of fun p q =>
    match p, q with
    | .inl e, .inl e' => if e' = e then -b e else 0
    | .inl e, .inr v => a e * ((if N.tail e = v then 1 else 0) - (if N.head e = v then 1 else 0))
    | .inr v, .inl e =>
      if v = N.sink then 0 else (if N.tail e = v then 1 else 0) - (if N.head e = v then 1 else 0)
    | .inr v, .inr v' =>
      if v = N.sink then (if v' = v then 1 else 0) else if v = N.source ∧ v' = v then -c else 0

theorem system_mulVec_inl (N : Network V E) (a b : E → R) (c : R) (u : E ⊕ V → R) (e : E) :
    (N.system a b c).mulVec u (.inl e) =
      a e * (u (.inr (N.tail e)) - u (.inr (N.head e))) - b e * u (.inl e) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, system, Matrix.of_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_sub, sub_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  ring

theorem system_mulVec_inr (N : Network V E) (a b : E → R) (c : R) (u : E ⊕ V → R) (v : V) :
    (N.system a b c).mulVec u (.inr v) =
      if v = N.sink then u (.inr N.sink)
      else N.div (fun e => u (.inl e)) v - if v = N.source then c * u (.inr N.source) else 0 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, system, Matrix.of_apply]
  by_cases hv : v = N.sink
  · subst hv
    simp
  · simp only [hv, ite_false, div, sub_mul, ite_mul, one_mul, zero_mul]
    by_cases hs : v = N.source
    · subst hs
      simp
      ring
    · simp [hs]

/-- The equations that a vector annihilated by the matrix of the system satisfies. -/
theorem system_mulVec_eq_zero (N : Network V E) {a b : E → R} {c : R} {u : E ⊕ V → R}
    (hu : (N.system a b c).mulVec u = 0) :
    (∀ e, a e * (u (.inr (N.tail e)) - u (.inr (N.head e))) = b e * u (.inl e)) ∧
      (∀ v, v ≠ N.sink →
        N.div (fun e => u (.inl e)) v = if v = N.source then c * u (.inr N.source) else 0) ∧
      u (.inr N.sink) = 0 := by
  refine ⟨fun e => ?_, fun v hv => ?_, ?_⟩
  · have := congrFun hu (.inl e)
    rw [system_mulVec_inl] at this
    exact sub_eq_zero.mp this
  · have := congrFun hu (.inr v)
    simp only [system_mulVec_inr, hv, ↓reduceIte] at this
    exact sub_eq_zero.mp this
  · have := congrFun hu (.inr N.sink)
    simp only [system_mulVec_inr, ↓reduceIte] at this
    exact this

omit [Fintype V] [Fintype E] in
theorem system_map {S : Type*} [CommRing S] (N : Network V E) (f : R →+* S) (a b : E → R) (c : R) :
    (N.system a b c).map f = N.system (fun e => f (a e)) (fun e => f (b e)) (f c) := by
  ext (p | p) (q | q) <;> simp only [system, Matrix.map_apply, Matrix.of_apply] <;> split_ifs <;> simp

/-- A vector annihilated by the system with unit coefficients on the potentials is a flow with the sink at potential zero. -/
theorem isFlow_of_mulVec (N : Network V E) (hst : N.source ≠ N.sink) {r : E → ℝ} {c : ℝ} {u : E ⊕ V → ℝ}
    (hu : (N.system (fun _ => 1) r c).mulVec u = 0) :
    N.IsFlow r (c * u (.inr N.source)) (fun v => u (.inr v)) (fun e => u (.inl e)) ∧
      u (.inr N.sink) = 0 := by
  obtain ⟨h1, h2, h3⟩ := N.system_mulVec_eq_zero hu
  exact ⟨⟨fun e => by simpa using h1 e, N.div_eq_of_ne_sink hst h2⟩, h3⟩

/-- For positive resistances the system of a flow has a non-zero determinant. -/
theorem Proper.det_system_pos {N : Network V E} (hN : N.Proper) {r : E → ℝ} (hr : ∀ e, 0 < r e) :
    (N.system (fun _ => 1) r 0).det ≠ 0 := by
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨hf, ht⟩ := N.isFlow_of_mulVec hN.source_ne_sink hu
  obtain ⟨h1, h2⟩ := hf.trivial_of_pos hN hr (by simp)
  apply hu0
  funext p
  rcases p with e | v
  · exact congrFun h1 e
  · simpa [ht] using h2 v

/-- For negative resistances the system of a flow whose value is the potential of the source has a non-zero determinant. -/
theorem Proper.det_system_neg {N : Network V E} (hN : N.Proper) {r : E → ℝ} (hr : ∀ e, r e < 0) :
    (N.system (fun _ => 1) r 1).det ≠ 0 := by
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨hf, ht⟩ := N.isFlow_of_mulVec hN.source_ne_sink hu
  obtain ⟨h1, h2⟩ := hf.trivial_of_neg hN hr (by
    simp only [ht, one_mul, sub_zero]
    exact mul_self_nonneg _)
  apply hu0
  funext p
  rcases p with e | v
  · exact congrFun h1 e
  · simpa [ht] using h2 v

/-- For positive resistances a connected network has a flow of every value. -/
theorem Proper.exists_isFlow {N : Network V E} (hN : N.Proper) {r : E → ℝ} (hr : ∀ e, 0 < r e) (I : ℝ) :
    ∃ φ i, N.IsFlow r I φ i := by
  have hunit : IsUnit (N.system (fun _ => 1) r 0) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hN.det_system_pos hr))
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
    (Sum.elim (fun _ => 0) fun v => if v = N.source then I else 0)
  refine ⟨fun v => u (.inr v), fun e => u (.inl e), fun e => ?_, N.div_eq_of_ne_sink hN.source_ne_sink ?_⟩
  · have := congrFun hu (.inl e)
    rw [system_mulVec_inl] at this
    simp only [Sum.elim_inl, one_mul] at this
    linarith
  · intro v hv
    have := congrFun hu (.inr v)
    simp only [system_mulVec_inr, hv, ↓reduceIte] at this
    simpa using this

open Classical in
/-- Impedance of a network between its poles: the potential difference between the poles in a flow of value one. -/
noncomputable def impedance (N : Network V E) (r : E → ℝ) : ℝ :=
  if h : ∃ φ i, N.IsFlow r 1 φ i then h.choose N.source - h.choose N.sink else 0

omit [DecidableEq E] in
/-- For positive resistances, the potential difference between the poles of a flow of non-zero value, divided by the value, is the impedance. -/
theorem IsFlow.impedance_eq {N : Network V E} {r : E → ℝ} {I : ℝ} {φ : V → ℝ} {i : E → ℝ} (hN : N.Proper)
    (hr : ∀ e, 0 < r e) (h : N.IsFlow r I φ i) (hI : I ≠ 0) :
    (φ N.source - φ N.sink) / I = N.impedance r := by
  have h1 := h.smul I⁻¹
  rw [inv_mul_cancel₀ hI] at h1
  have hex : ∃ φ i, N.IsFlow r 1 φ i := ⟨_, _, h1⟩
  simp only [impedance, hex, ↓reduceDIte]
  obtain ⟨-, h2⟩ := hex.choose_spec.choose_spec.unique hN hr h1
  have h3 := h2 N.source
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  have h4 : hex.choose N.source - hex.choose N.sink = I⁻¹ * (φ N.source - φ N.sink) := by
    linear_combination h3
  rw [h4]
  field_simp

/-- The impedance of a connected network with positive resistances is positive. -/
theorem Proper.impedance_pos {N : Network V E} (hN : N.Proper) {r : E → ℝ} (hr : ∀ e, 0 < r e) :
    0 < N.impedance r := by
  obtain ⟨φ, i, h⟩ := hN.exists_isFlow hr 1
  rw [← h.impedance_eq hN hr one_ne_zero, div_one]
  by_contra hle
  obtain ⟨h1, -⟩ := h.trivial_of_pos hN hr (by rw [one_mul]; exact not_lt.mp hle)
  have h2 := h.kirchhoff N.source
  rw [h1] at h2
  simp [div, hN.source_ne_sink] at h2

end Network

end Rectiling
