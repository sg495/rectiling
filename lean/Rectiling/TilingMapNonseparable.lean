-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.TilingMapFlow

/-!
# The map of a tiling is non-separable

The map of a tiling of a rectangle is connected, has no loop, and has no vertex whose removal disconnects it.
From every vertex the top ends of the tiles lead down to the bottom side of the main rectangle and the bottom ends lead up to its top side, and the two sides are joined by the additional edge.
The network of the map is connected as well.
-/

namespace Rectiling

open Classical

/-- A set that a permutation of a finite set preserves and on which a function increases strictly along the permutation is empty. -/
theorem not_mem_of_strictMono {D : Type*} [Finite D] (π : Equiv.Perm D) (f : D → ℝ) (S : D → Prop)
    (hS : ∀ d, S d → S (π d) ∧ f d < f (π d)) (d : D) : ¬S d := by
  intro hd
  have key : ∀ k : ℕ, S ((π ^ (k + 1)) d) ∧ f d < f ((π ^ (k + 1)) d) := by
    intro k
    induction k with
    | zero => simpa using hS d hd
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(hS _ ih.1).1, ih.2.trans (hS _ ih.1).2⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos π).ne'
  have h1 := (key k).2
  rw [← Nat.succ_eq_add_one, ← hk, pow_orderOf_eq_one] at h1
  exact lt_irrefl _ h1

namespace CMap

variable {D : Type*} [Finite D] {M : CMap D} {P : D → Prop}

/-- A dart leads to every dart of its vertex by steps of the rotation. -/
theorem reach_of_sameCycle {a b : D} (h : M.σ.SameCycle a b) :
    Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) a b :=
  sameCycle_induction h (fun d => Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) a d)
    Relation.ReflTransGen.refl fun _ hd => hd.tail (Or.inl rfl)

/-- A path of steps of the rotation and of steps along the edges that arrive in a set of darts that the rotation preserves can be reversed, when it starts in the set. -/
theorem reach_symm (hP : ∀ a, P a → P (M.σ a)) {a b : D}
    (h : Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) a b) (ha : P a) :
    Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) b a ∧ P b := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, ha⟩
  | @tail x c _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases hbc with rfl | ⟨rfl, hc⟩
    · exact ⟨(reach_of_sameCycle (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))).trans ih1,
        hP _ ih2⟩
    · exact ⟨Relation.ReflTransGen.head (Or.inr ⟨(M.α_invol _).symm, ih2⟩) ih1, hc⟩

end CMap

variable {W H : ℝ} {tl : List Rect} {M : CMap (Dart tl.length)}

local notation "Lx" e:max => Rect.x (List.get tl e)
local notation "Rx" e:max => (Rect.x (List.get tl e) + Rect.w (List.get tl e))
local notation "By" e:max => Rect.y (List.get tl e)
local notation "Ty" e:max => (Rect.y (List.get tl e) + Rect.h (List.get tl e))

namespace IsTilingMap

/-- Every vertex contains the top end of a tile or the end of the additional edge on the bottom side. -/
theorem exists_top_or_poleBot (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl)
    (d : Dart tl.length) : (∃ e, M.σ.SameCycle d (some e, true)) ∨ M.σ.SameCycle d (none, false) := by
  by_contra hno
  rw [not_or, not_exists] at hno
  obtain ⟨hno1, hno2⟩ := hno
  have h3 : ¬M.σ.SameCycle d (none, true) := fun hc => by
    obtain ⟨e', he, -⟩ := hM.rotation.poleTop
    refine hno1 e' ?_
    rw [← he]
    exact Equiv.Perm.sameCycle_apply_right.mpr hc
  refine not_mem_of_strictMono M.σ (fun x => -dartStart W tl x) (fun x => M.σ.SameCycle d x)
    (fun x hx => ⟨Equiv.Perm.sameCycle_apply_right.mpr hx, ?_⟩) d (Equiv.Perm.SameCycle.refl _ _)
  rcases x with ⟨_ | e, _ | _⟩
  · exact absurd hx hno2
  · exact absurd hx h3
  · rw [hM.rotation.start]
    simp only [dartStart, dartStop]
    linarith [(h.get_bounds e).1]
  · exact absurd hx (hno1 e)

/-- Every vertex contains the bottom end of a tile or the end of the additional edge on the top side. -/
theorem exists_bot_or_poleTop (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl)
    (d : Dart tl.length) : (∃ e, M.σ.SameCycle d (some e, false)) ∨ M.σ.SameCycle d (none, true) := by
  by_contra hno
  rw [not_or, not_exists] at hno
  obtain ⟨hno1, hno2⟩ := hno
  have h3 : ¬M.σ.SameCycle d (none, false) := fun hc => by
    obtain ⟨e', he, -⟩ := hM.rotation.poleBot
    refine hno1 e' ?_
    rw [← he]
    exact Equiv.Perm.sameCycle_apply_right.mpr hc
  refine not_mem_of_strictMono M.σ (fun x => dartStart W tl x) (fun x => M.σ.SameCycle d x)
    (fun x hx => ⟨Equiv.Perm.sameCycle_apply_right.mpr hx, ?_⟩) d (Equiv.Perm.SameCycle.refl _ _)
  rcases x with ⟨_ | e, _ | _⟩
  · exact absurd hx h3
  · exact absurd hx hno2
  · exact absurd hx (hno1 e)
  · rw [hM.rotation.start]
    simp only [dartStart, dartStop]
    linarith [(h.get_bounds e).1]

/-- Every dart leads down to the additional edge on the bottom side, by steps of the rotation and steps from the top end of a tile to its bottom end, which may be required to arrive in a given set of darts that contains the bottom ends below the dart. -/
theorem reach_poleBot (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl)
    (P : Dart tl.length → Prop) (d : Dart tl.length)
    (hP : ∀ e, By e < dartHeight H tl d → P (some e, false)) :
    Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) d (none, false) := by
  have key : ∀ (k : ℕ) (d : Dart tl.length),
      (Finset.univ.filter fun x : Dart tl.length => dartHeight H tl x < dartHeight H tl d).card = k →
      (∀ e, By e < dartHeight H tl d → P (some e, false)) →
      Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) d (none, false) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro d hk hP
      rcases hM.exists_top_or_poleBot h d with ⟨e, he⟩ | hb
      · have h1 : dartHeight H tl d = Ty e := hM.height_eq he
        have hlt : By e < dartHeight H tl d := by
          rw [h1]
          linarith [(h.get_bounds e).2.1]
        refine (CMap.reach_of_sameCycle he).trans (Relation.ReflTransGen.head
          (Or.inr ⟨(hM.alpha (some e, true)).symm, hP e hlt⟩) (ih _ ?_ (some e, false) rfl fun e' he' =>
            hP e' (lt_trans he' hlt)))
        rw [← hk]
        refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).mpr
          ⟨(some e, false), ?_, ?_⟩)
        · rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, lt_trans hx.2 hlt⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hlt⟩
        · rw [Finset.mem_filter]
          exact fun hx => lt_irrefl _ hx.2
      · exact CMap.reach_of_sameCycle hb
  exact key _ d rfl hP

/-- Every dart leads up to the additional edge on the top side, by steps of the rotation and steps from the bottom end of a tile to its top end, which may be required to arrive in a given set of darts that contains the top ends above the dart. -/
theorem reach_poleTop (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl)
    (P : Dart tl.length → Prop) (d : Dart tl.length)
    (hP : ∀ e, dartHeight H tl d < Ty e → P (some e, true)) :
    Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) d (none, true) := by
  have key : ∀ (k : ℕ) (d : Dart tl.length),
      (Finset.univ.filter fun x : Dart tl.length => dartHeight H tl d < dartHeight H tl x).card = k →
      (∀ e, dartHeight H tl d < Ty e → P (some e, true)) →
      Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ P b)) d (none, true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro d hk hP
      rcases hM.exists_bot_or_poleTop h d with ⟨e, he⟩ | hb
      · have h1 : dartHeight H tl d = By e := hM.height_eq he
        have hlt : dartHeight H tl d < Ty e := by
          rw [h1]
          linarith [(h.get_bounds e).2.1]
        refine (CMap.reach_of_sameCycle he).trans (Relation.ReflTransGen.head
          (Or.inr ⟨(hM.alpha (some e, false)).symm, hP e hlt⟩) (ih _ ?_ (some e, true) rfl fun e' he' =>
            hP e' (lt_trans hlt he')))
        rw [← hk]
        refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).mpr
          ⟨(some e, true), ?_, ?_⟩)
        · rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, lt_trans hlt hx.2⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hlt⟩
        · rw [Finset.mem_filter]
          exact fun hx => lt_irrefl _ hx.2
      · exact CMap.reach_of_sameCycle hb
  exact key _ d rfl hP

/-- The map of a tiling is connected. -/
theorem connected (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) : M.Connected := by
  intro d d'
  have h1 := fun x => hM.reach_poleBot h (fun _ => True) x fun _ _ => trivial
  have h2 := (CMap.reach_symm (M := M) (P := fun _ => True) (fun _ _ => trivial) (h1 d') trivial).1
  refine ((h1 d).trans h2).lift id ?_
  rintro a b (hab | ⟨hab, -⟩)
  · exact Or.inl hab
  · exact Or.inr hab

/-- The map of a tiling has no loop. -/
theorem loopless (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hH : 0 < H) :
    M.Loopless := by
  intro d hd
  rw [hM.alpha] at hd
  rcases d with ⟨_ | e, _ | _⟩
  · have h1 : (0 : ℝ) = H := hM.height_eq hd
    exact hH.ne h1
  · have h1 : H = (0 : ℝ) := hM.height_eq hd
    exact hH.ne' h1
  · have h1 : By e = Ty e := hM.height_eq hd
    linarith [(h.get_bounds e).2.1]
  · have h1 : Ty e = By e := hM.height_eq hd
    linarith [(h.get_bounds e).2.1]

/-- The map of a tiling has no vertex whose removal disconnects it. -/
theorem noCutVertex (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) : M.NoCutVertex := by
  intro u d d' hd hd'
  have hPσ : ∀ a, ¬M.σ.SameCycle u a → ¬M.σ.SameCycle u (M.σ a) := fun a ha hc =>
    ha (Equiv.Perm.sameCycle_apply_right.mp hc)
  have reach : ∀ x, ¬M.σ.SameCycle u x →
      Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ ¬M.σ.SameCycle u b)) x (none, false) ∨
      Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ ¬M.σ.SameCycle u b)) x (none, true) := by
    intro x _
    rcases le_total (dartHeight H tl x) (dartHeight H tl u) with hle | hle
    · left
      refine hM.reach_poleBot h (fun b => ¬M.σ.SameCycle u b) x fun e he hc => ?_
      have h1 : dartHeight H tl u = By e := hM.height_eq hc
      linarith
    · right
      refine hM.reach_poleTop h (fun b => ¬M.σ.SameCycle u b) x fun e he hc => ?_
      have h1 : dartHeight H tl u = Ty e := hM.height_eq hc
      linarith
  have join : ∀ x y, ¬M.σ.SameCycle u y →
      Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ ¬M.σ.SameCycle u b)) x (none, false) →
      Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ ¬M.σ.SameCycle u b)) y (none, true) →
      Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ ¬M.σ.SameCycle u b)) x y := by
    intro x y hy h1 h2
    have h3 := CMap.reach_symm (M := M) (P := fun b => ¬M.σ.SameCycle u b) hPσ h2 hy
    exact (h1.tail (Or.inr ⟨(hM.alpha (none, false)).symm, h3.2⟩)).trans h3.1
  rcases reach d hd with h1 | h1 <;> rcases reach d' hd' with h2 | h2
  · exact h1.trans (CMap.reach_symm (M := M) (P := fun b => ¬M.σ.SameCycle u b) hPσ h2 hd').1
  · exact join d d' hd' h1 h2
  · exact (CMap.reach_symm (M := M) (P := fun b => ¬M.σ.SameCycle u b) hPσ (join d' d hd h2 h1) hd').1
  · exact h1.trans (CMap.reach_symm (M := M) (P := fun b => ¬M.σ.SameCycle u b) hPσ h2 hd').1

/-- The network of the map of a tiling has distinct poles, no loop, and is connected. -/
theorem tilingNet_proper (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hH : 0 < H) :
    (tilingNet M).Proper where
  source_ne_sink := hM.source_ne_sink hH
  loopless e he := by
    have h1 : Ty e = By e := hM.height_eq (M.vertex_eq_iff.mp he)
    linarith [(h.get_bounds e).2.1]
  connected v := by
    obtain ⟨d, rfl⟩ := M.vertex_surjective v
    have h1 := hM.reach_poleBot h (fun b => b.1 ≠ none) d fun e _ => Option.some_ne_none e
    have lift : ∀ a b : Dart tl.length,
        Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ b.1 ≠ none)) a b →
        Relation.ReflTransGen (tilingNet M).Adj (M.vertex a) (M.vertex b) := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | @tail x c _ hbc ih =>
        rcases hbc with rfl | ⟨rfl, hc⟩
        · rw [M.vertex_σ]
          exact ih
        · refine ih.tail ?_
          rw [hM.alpha] at hc ⊢
          rcases x with ⟨_ | e, _ | _⟩
          · exact absurd rfl hc
          · exact absurd rfl hc
          · exact ⟨e, Or.inr ⟨rfl, rfl⟩⟩
          · exact ⟨e, Or.inl ⟨rfl, rfl⟩⟩
    exact lift _ _ h1

end IsTilingMap

end Rectiling
