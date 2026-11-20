-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.TilingMapNonseparable

/-!
# The map of a tiling is planar

The numbers of vertices, edges and faces of the map of a tiling of a rectangle satisfy the formula of Euler for the sphere.
Each vertex other than the two poles contains exactly one top end of a tile that is followed by a bottom end, at the right end of its horizontal segment; each face other than the two that contain the additional edge contains exactly one bottom end of a tile whose top end is followed by a top end, at the top end of a vertical segment.
Since the top end of every tile but one is followed by a bottom end or by a top end, the vertices and the faces are three more than the tiles.
-/

namespace Rectiling

open Classical

/-- The cycles of a permutation are as many as the elements of a set that meets every cycle exactly once. -/
theorem card_cycles_eq {D : Type*} (π : Equiv.Perm D) (p : D → Prop) (h1 : ∀ d, ∃ m, p m ∧ π.SameCycle d m)
    (h2 : ∀ m m', p m → p m' → π.SameCycle m m' → m = m') :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid π)) = Nat.card {m // p m} := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun m : {m // p m} => (Quotient.mk (Equiv.Perm.SameCycle.setoid π) m.1)) ⟨?_, ?_⟩)).symm
  · intro m m' heq
    exact Subtype.ext (h2 _ _ m.2 m'.2 (Quotient.eq.mp heq))
  · intro q
    induction q using Quotient.inductionOn with
    | _ d =>
      obtain ⟨m, hm, hc⟩ := h1 d
      exact ⟨⟨m, hm⟩, Quotient.sound hc.symm⟩

variable {W H : ℝ} {tl : List Rect} {M : CMap (Dart tl.length)}

local notation "Lx" e:max => Rect.x (List.get tl e)
local notation "Rx" e:max => (Rect.x (List.get tl e) + Rect.w (List.get tl e))
local notation "By" e:max => Rect.y (List.get tl e)
local notation "Ty" e:max => (Rect.y (List.get tl e) + Rect.h (List.get tl e))

/-- The darts that mark the vertices: the two ends of the additional edge, and the top ends of the tiles that are followed by a bottom end. -/
def vertexMark (M : CMap (Dart tl.length)) : Dart tl.length → Prop
  | (none, _) => True
  | (some e, true) => ∃ e', M.σ (some e, true) = (some e', false)
  | (some _, false) => False

/-- The darts that mark the faces: the two ends of the additional edge, and the bottom ends of the tiles whose top end is followed by a top end. -/
def faceMark (M : CMap (Dart tl.length)) : Dart tl.length → Prop
  | (none, _) => True
  | (some e, false) => ∃ e', M.σ (some e, true) = (some e', true)
  | (some _, true) => False

namespace IsTilingMap

theorem face_apply (hM : IsTilingMap W H tl M) (d : Dart tl.length) : M.face d = M.σ (d.1, !d.2) := by
  rw [← hM.alpha]
  rfl

/-- The face permutation preserves the abscissa at which a dart starts. -/
theorem start_face (hM : IsTilingMap W H tl M) (d : Dart tl.length) :
    dartStart W tl (M.face d) = dartStart W tl d := by
  rw [hM.face_apply, hM.rotation.start]
  rcases d with ⟨_ | e, _ | _⟩ <;> rfl

/-- The face permutation sends a dart to a dart at the height of the other end of its edge. -/
theorem height_face (hM : IsTilingMap W H tl M) (d : Dart tl.length) :
    dartHeight H tl (M.face d) = dartHeight H tl (d.1, !d.2) := by
  rw [hM.face_apply, hM.rotation.height]

/-- The darts of a face start at the same abscissa. -/
theorem start_eq (hM : IsTilingMap W H tl M) {a b : Dart tl.length} (hab : M.face.SameCycle a b) :
    dartStart W tl a = dartStart W tl b :=
  sameCycle_induction hab (fun d => dartStart W tl a = dartStart W tl d) rfl fun d hd => by
    rw [hM.start_face]
    exact hd

/-- The darts of the vertex of a top end that is followed by a bottom end do not extend to the right of that top end. -/
theorem vertex_closure (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) {e e' : Fin tl.length}
    (hσ : M.σ (some e, true) = (some e', false)) {d : Dart tl.length}
    (hd : M.σ.SameCycle (some e, true) d) : dartStop W tl d ≤ Rx e := by
  obtain ⟨ew, eh, ex0, exW, ey0, eyH⟩ := h.get_bounds e
  refine (sameCycle_induction hd (fun d => dartHeight H tl d = Ty e ∧ dartStart W tl d ≤ Rx e ∧
    dartStop W tl d ≤ Rx e) ⟨rfl, ?_, le_rfl⟩ ?_).2.2
  · change Lx e ≤ Rx e
    linarith
  intro d ⟨hh, hs, ht⟩
  have hh' := hM.rotation.height d
  have hs' := hM.rotation.start d
  rw [hh] at hh'
  generalize hd' : M.σ d = d' at hh' hs' ⊢
  have hs2 : dartStart W tl d' ≤ Rx e := by
    rw [hs']
    exact ht
  refine ⟨hh', hs2, ?_⟩
  rcases d' with ⟨_ | u, _ | _⟩
  · have h1 : (0 : ℝ) = Ty e := hh'
    linarith
  · change (0 : ℝ) ≤ Rx e
    linarith
  · have h1 : Rx u ≤ Rx e := hs2
    change Lx u ≤ Rx e
    linarith [(h.get_bounds u).1]
  · have hT : Ty u = Ty e := hh'
    have hL : Lx u ≤ Rx e := hs2
    change Rx u ≤ Rx e
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨uw, uh, -⟩ := h.get_bounds u
    rcases hL.lt_or_eq with hlt | heq
    · have := h.eq_of_overlap (e := u) (e' := e) hlt (by linarith) (by linarith) (by linarith)
      subst this
      linarith
    · have hstop : dartStop W tl d = Rx e := by
        rw [← hs']
        exact heq
      rcases d with ⟨_ | u₀, _ | _⟩
      · have h1 : (0 : ℝ) = Ty e := hh
        linarith
      · have h1 : (0 : ℝ) = Rx e := hstop
        linarith
      · have h1 : Lx u₀ = Rx e := hstop
        have h2 : Rx u₀ ≤ Rx e := hs
        linarith [(h.get_bounds u₀).1]
      · have h1 : Rx u₀ = Rx e := hstop
        have h2 : Ty u₀ = Ty e := hh
        have := h.eq_of_top_right h2 h1
        subst this
        rw [hσ] at hd'
        exact absurd hd' (by simp)

/-- The edges of the face of a bottom end whose top end is followed by a top end do not extend above that top end. -/
theorem face_closure (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) {e e₁ : Fin tl.length}
    (hσ : M.σ (some e, true) = (some e₁, true)) {d : Dart tl.length}
    (hd : M.face.SameCycle (some e, false) d) : dartHeight H tl (d.1, !d.2) ≤ Ty e := by
  obtain ⟨ew, eh, ex0, exW, ey0, eyH⟩ := h.get_bounds e
  refine (sameCycle_induction hd (fun d => dartStart W tl d = Rx e ∧ dartHeight H tl d ≤ Ty e ∧
    dartHeight H tl (d.1, !d.2) ≤ Ty e) ⟨rfl, ?_, le_rfl⟩ ?_).2.2
  · change By e ≤ Ty e
    linarith
  intro d ⟨hs, hh, ht⟩
  have hs' := hM.start_face d
  have hh' := hM.height_face d
  have hd' := hM.face_apply d
  rw [hs] at hs'
  generalize M.face d = d' at hs' hh' hd' ⊢
  have hh2 : dartHeight H tl d' ≤ Ty e := by
    rw [hh']
    exact ht
  refine ⟨hs', hh2, ?_⟩
  rcases d' with ⟨_ | u, _ | _⟩
  · have h1 : (0 : ℝ) = Rx e := hs'
    linarith
  · change (0 : ℝ) ≤ Ty e
    linarith
  · have hR : Rx u = Rx e := hs'
    have hB : By u ≤ Ty e := hh2
    change Ty u ≤ Ty e
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨uw, uh, -⟩ := h.get_bounds u
    rcases hB.lt_or_eq with hlt | heq
    · have := h.eq_of_overlap (e := u) (e' := e) (by linarith) (by linarith) hlt (by linarith)
      subst this
      linarith
    · have hflip : dartHeight H tl (d.1, !d.2) = Ty e := by
        rw [← hh']
        exact heq
      rcases d with ⟨_ | u₀, _ | _⟩
      · have h1 : (0 : ℝ) = Rx e := hs
        linarith
      · have h1 : (0 : ℝ) = Ty e := hflip
        linarith
      · have h1 : Ty u₀ = Ty e := hflip
        have h2 : Rx u₀ = Rx e := hs
        have := h.eq_of_top_right h1 h2
        subst this
        have hd2 : (some u, false) = M.σ (some u₀, true) := hd'
        rw [hσ] at hd2
        exact absurd hd2 (by simp)
      · have h1 : By u₀ = Ty e := hflip
        have h2 : Ty u₀ ≤ Ty e := hh
        linarith [(h.get_bounds u₀).2.1]
  · have hT : Ty u ≤ Ty e := hh2
    change By u ≤ Ty e
    linarith [(h.get_bounds u).2.1]

/-- Every vertex contains a dart that marks the vertices. -/
theorem exists_vertexMark (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (d : Dart tl.length) :
    ∃ m, vertexMark M m ∧ M.σ.SameCycle d m := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have htop : ∀ x, ¬(M.σ.SameCycle d x ∧ ∃ e, x = (some e, true)) := by
    refine not_mem_of_strictMono M.σ (dartStart W tl) _ ?_
    rintro x ⟨hx, e, rfl⟩
    rcases hM.rotation.top e with ⟨a, ha, -, -⟩ | ⟨a, ha, -, -⟩ | ⟨ha, -, -⟩
    · refine ⟨⟨Equiv.Perm.sameCycle_apply_right.mpr hx, a, ha⟩, ?_⟩
      rw [hM.rotation.start]
      change Lx e < Rx e
      linarith [(h.get_bounds e).1]
    · exact absurd hx (hno _ ⟨a, ha⟩)
    · refine absurd ?_ (hno (none, true) trivial)
      rw [← ha]
      exact Equiv.Perm.sameCycle_apply_right.mpr hx
  refine not_mem_of_strictMono M.σ (fun x => -dartStart W tl x) (fun x => M.σ.SameCycle d x)
    (fun x hx => ⟨Equiv.Perm.sameCycle_apply_right.mpr hx, ?_⟩) d (Equiv.Perm.SameCycle.refl _ _)
  rcases x with ⟨_ | e, _ | _⟩
  · exact absurd hx (hno _ trivial)
  · exact absurd hx (hno _ trivial)
  · rw [hM.rotation.start]
    change -Rx e < -Lx e
    linarith [(h.get_bounds e).1]
  · exact absurd ⟨hx, e, rfl⟩ (htop _)

/-- Every face contains a dart that marks the faces. -/
theorem exists_faceMark (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (d : Dart tl.length) :
    ∃ m, faceMark M m ∧ M.face.SameCycle d m := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hbot : ∀ x, ¬(M.face.SameCycle d x ∧ ∃ e, x = (some e, false)) := by
    refine not_mem_of_strictMono M.face (dartHeight H tl) _ ?_
    rintro x ⟨hx, e, rfl⟩
    have hf : M.face (some e, false) = M.σ (some e, true) := hM.face_apply _
    rcases hM.rotation.top e with ⟨a, ha, -, -⟩ | ⟨a, ha, ha1, -⟩ | ⟨ha, -, -⟩
    · exact absurd hx (hno _ ⟨a, ha⟩)
    · refine ⟨⟨Equiv.Perm.sameCycle_apply_right.mpr hx, a, hf.trans ha⟩, ?_⟩
      rw [hf, ha]
      change By e < By a
      linarith [(h.get_bounds e).2.1]
    · refine absurd ?_ (hno (none, true) trivial)
      rw [← ha, ← hf]
      exact Equiv.Perm.sameCycle_apply_right.mpr hx
  refine not_mem_of_strictMono M.face (fun x => -dartHeight H tl x) (fun x => M.face.SameCycle d x)
    (fun x hx => ⟨Equiv.Perm.sameCycle_apply_right.mpr hx, ?_⟩) d (Equiv.Perm.SameCycle.refl _ _)
  rcases x with ⟨_ | e, _ | _⟩
  · exact absurd hx (hno _ trivial)
  · exact absurd hx (hno _ trivial)
  · exact absurd ⟨hx, e, rfl⟩ (hbot _)
  · have hf : M.face (some e, true) = M.σ (some e, false) := hM.face_apply _
    have hx' := Equiv.Perm.sameCycle_apply_right.mpr hx
    rcases hM.rotation.bot e with ⟨a, ha, -, -⟩ | ⟨a, ha, ha1, -⟩ | ⟨ha, -, -⟩
    · exact absurd ⟨hx', a, hf.trans ha⟩ (hbot _)
    · rw [hf, ha]
      change -Ty e < -Ty a
      linarith [(h.get_bounds e).2.1]
    · refine absurd ?_ (hno (none, false) trivial)
      rw [← ha, ← hf]
      exact hx'

/-- A vertex contains at most one dart that marks the vertices. -/
theorem vertexMark_unique (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hH : 0 < H)
    {m m' : Dart tl.length} (hm : vertexMark M m) (hm' : vertexMark M m') (hc : M.σ.SameCycle m m') :
    m = m' := by
  have key : ∀ (e e' : Fin tl.length), M.σ (some e, true) = (some e', false) → 0 < Ty e ∧ Ty e < H := by
    intro e e' he
    have h1 : By e' = Ty e := by
      have := hM.rotation.height (some e, true)
      rw [he] at this
      exact this
    exact ⟨by linarith [(h.get_bounds e).2.1, (h.get_bounds e).2.2.2.2.1],
      by linarith [(h.get_bounds e').2.1, (h.get_bounds e').2.2.2.2.2]⟩
  have hh := hM.height_eq hc
  rcases m with ⟨_ | e, _ | _⟩ <;> rcases m' with ⟨_ | e₂, _ | _⟩
  · rfl
  · exact absurd (hh : (0 : ℝ) = H) hH.ne
  · exact hm'.elim
  · obtain ⟨a, ha⟩ := hm'
    have h1 : (0 : ℝ) = Ty e₂ := hh
    linarith [(key e₂ a ha).1]
  · exact absurd (hh : H = (0 : ℝ)) hH.ne'
  · rfl
  · exact hm'.elim
  · obtain ⟨a, ha⟩ := hm'
    have h1 : H = Ty e₂ := hh
    linarith [(key e₂ a ha).2]
  · exact hm.elim
  · exact hm.elim
  · exact hm.elim
  · exact hm.elim
  · obtain ⟨a, ha⟩ := hm
    have h1 : Ty e = (0 : ℝ) := hh
    linarith [(key e a ha).1]
  · obtain ⟨a, ha⟩ := hm
    have h1 : Ty e = H := hh
    linarith [(key e a ha).2]
  · exact hm'.elim
  · obtain ⟨a, ha⟩ := hm
    obtain ⟨a₂, ha₂⟩ := hm'
    have h1 : Rx e₂ ≤ Rx e := hM.vertex_closure h ha hc
    have h2 : Rx e ≤ Rx e₂ := hM.vertex_closure h ha₂ hc.symm
    rw [h.eq_of_top_right (hh : Ty e = Ty e₂) (le_antisymm h2 h1)]

/-- A face contains at most one dart that marks the faces. -/
theorem faceMark_unique (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hW : 0 < W)
    {m m' : Dart tl.length} (hm : faceMark M m) (hm' : faceMark M m') (hc : M.face.SameCycle m m') :
    m = m' := by
  have key : ∀ (e e' : Fin tl.length), M.σ (some e, true) = (some e', true) → 0 < Rx e ∧ Rx e < W := by
    intro e e' he
    have h1 : Lx e' = Rx e := by
      have := hM.rotation.start (some e, true)
      rw [he] at this
      exact this
    exact ⟨by linarith [(h.get_bounds e).1, (h.get_bounds e).2.2.1],
      by linarith [(h.get_bounds e').1, (h.get_bounds e').2.2.2.1]⟩
  have hs := hM.start_eq hc
  rcases m with ⟨_ | e, _ | _⟩ <;> rcases m' with ⟨_ | e₂, _ | _⟩
  · rfl
  · exact absurd (hs : (0 : ℝ) = W) hW.ne
  · obtain ⟨a, ha⟩ := hm'
    have h1 : (0 : ℝ) = Rx e₂ := hs
    linarith [(key e₂ a ha).1]
  · exact hm'.elim
  · exact absurd (hs : W = (0 : ℝ)) hW.ne'
  · rfl
  · obtain ⟨a, ha⟩ := hm'
    have h1 : W = Rx e₂ := hs
    linarith [(key e₂ a ha).2]
  · exact hm'.elim
  · obtain ⟨a, ha⟩ := hm
    have h1 : Rx e = (0 : ℝ) := hs
    linarith [(key e a ha).1]
  · obtain ⟨a, ha⟩ := hm
    have h1 : Rx e = W := hs
    linarith [(key e a ha).2]
  · obtain ⟨a, ha⟩ := hm
    obtain ⟨a₂, ha₂⟩ := hm'
    have h1 : Ty e₂ ≤ Ty e := hM.face_closure h ha hc
    have h2 : Ty e ≤ Ty e₂ := hM.face_closure h ha₂ hc.symm
    rw [h.eq_of_top_right (le_antisymm h2 h1) (hs : Rx e = Rx e₂)]
  · exact hm'.elim
  · exact hm.elim
  · exact hm.elim
  · exact hm.elim
  · exact hm.elim

/-- The number of vertices of the map of a tiling: two more than the tiles whose top end is followed by a bottom end. -/
theorem card_vertex (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hH : 0 < H) :
    Nat.card M.Vertex =
      2 + ∑ e : Fin tl.length, if ∃ e', M.σ (some e, true) = (some e', false) then 1 else 0 := by
  have h1 : Nat.card M.Vertex = Nat.card {m // vertexMark M m} :=
    card_cycles_eq M.σ (vertexMark M) (hM.exists_vertexMark h) fun _ _ hm hm' hc =>
      hM.vertexMark_unique h hH hm hm' hc
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool, vertexMark, ↓reduceIte, add_zero,
    Nat.reduceAdd]
  refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
  by_cases hc : ∃ e', M.σ (some e, true) = (some e', false) <;> simp [hc]

/-- The number of faces of the map of a tiling: two more than the tiles whose top end is followed by a top end. -/
theorem card_face (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) :
    Nat.card M.Face =
      2 + ∑ e : Fin tl.length, if ∃ e', M.σ (some e, true) = (some e', true) then 1 else 0 := by
  have h1 : Nat.card M.Face = Nat.card {m // faceMark M m} :=
    card_cycles_eq M.face (faceMark M) (hM.exists_faceMark h) fun _ _ hm hm' hc =>
      hM.faceMark_unique h hW hm hm' hc
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool, faceMark, ↓reduceIte, zero_add,
    Nat.reduceAdd]
  refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
  by_cases hc : ∃ e', M.σ (some e, true) = (some e', true) <;> simp [hc]

/-- The top end of exactly one tile is followed by the additional edge. -/
theorem sum_poleTop (hM : IsTilingMap W H tl M) :
    ∑ e : Fin tl.length, (if M.σ (some e, true) = (none, true) then 1 else 0) = 1 := by
  have hx : M.σ (M.σ.symm (none, true)) = (none, true) := M.σ.apply_symm_apply _
  generalize M.σ.symm (none, true) = x at hx
  rcases x with ⟨_ | u, _ | _⟩
  · obtain ⟨a, ha, -⟩ := hM.rotation.poleBot
    rw [ha] at hx
    exact absurd hx (by simp)
  · obtain ⟨a, ha, -⟩ := hM.rotation.poleTop
    rw [ha] at hx
    exact absurd hx (by simp)
  · rcases hM.rotation.bot u with ⟨a, ha, -, -⟩ | ⟨a, ha, -, -⟩ | ⟨ha, -, -⟩ <;> rw [ha] at hx <;>
      exact absurd hx (by simp)
  · have h1 : ∀ e : Fin tl.length, (M.σ (some e, true) = (none, true)) = (e = u) := by
      intro e
      refine propext ⟨fun he => ?_, fun he => by rw [he, hx]⟩
      have := M.σ.injective (he.trans hx.symm)
      simpa using this
    simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The edges of the map of a tiling are one more than the tiles. -/
theorem card_edge (hM : IsTilingMap W H tl M) : Nat.card M.Edge = tl.length + 1 := by
  have hfst : ∀ a b : Dart tl.length, M.α.SameCycle a b → a.1 = b.1 := fun a b hab =>
    sameCycle_induction hab (fun d => a.1 = d.1) rfl fun d hd => by
      rw [hM.alpha]
      exact hd
  let f : M.Edge ≃ Option (Fin tl.length) :=
    { toFun := Quotient.lift (fun d : Dart tl.length => d.1) hfst
      invFun := fun o => M.edge (o, true)
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | _ d =>
          rcases d with ⟨o, _ | _⟩
          · exact (M.edge_eq_iff.mpr (Or.inr (hM.alpha (o, true)).symm))
          · rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]

/-- The map of a tiling is connected and satisfies the formula of Euler for the sphere. -/
theorem planar (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hW : 0 < W) (hH : 0 < H) :
    M.Planar := by
  refine ⟨hM.connected h, ?_⟩
  rw [hM.card_vertex h hH, hM.card_face h hW, hM.card_edge]
  have h1 : ∀ e : Fin tl.length,
      (if ∃ e', M.σ (some e, true) = (some e', false) then 1 else 0) +
        (if ∃ e', M.σ (some e, true) = (some e', true) then 1 else 0) +
        (if M.σ (some e, true) = (none, true) then 1 else 0) = 1 := by
    intro e
    rcases hM.rotation.top e with ⟨a, ha, -, -⟩ | ⟨a, ha, -, -⟩ | ⟨ha, -, -⟩ <;> simp [ha]
  have h2 := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin tl.length))) rfl fun e _ => h1 e
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hM.sum_poleTop] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
  omega

end IsTilingMap

end Rectiling
