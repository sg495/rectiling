-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.ProportionBound
import Rectiling.CombinatorialMap

/-!
# The network and the polynomial of a rooted map

The polynomial of a network with an orientation vector does not depend on the reference directions of the edges.
A combinatorial map with a root has a network, whose vertices are those of the map, whose edges are the edges other than that of the root, and whose poles are the two ends of the edge of the root; an isomorphism of rooted maps carries the polynomials of one to those of the other.
The proportions attached to a rooted map are the roots of its polynomials for the orientation vectors in which the edge before the root is wide, and they depend only on the class of the rooted map.
-/

namespace Rectiling

namespace Network

open Polynomial

variable {V E V' E' : Type*}

/-- The network with the reference directions of a set of edges reversed. -/
def reverse (N : Network V E) (S : E → Prop) [DecidablePred S] : Network V E where
  tail e := if S e then N.head e else N.tail e
  head e := if S e then N.tail e else N.head e
  source := N.source
  sink := N.sink

/-- Correspondence of networks that disregards the reference directions: bijections between the vertices and between the edges that respect the pairs of ends of the edges, and the poles. -/
structure UIso (N : Network V E) (N' : Network V' E') where
  /-- The bijection between the vertices. -/
  toV : V ≃ V'
  /-- The bijection between the edges. -/
  toE : E ≃ E'
  /-- The ends of corresponding edges correspond, in the same or in the opposite direction. -/
  ends : ∀ e, (N'.tail (toE e) = toV (N.tail e) ∧ N'.head (toE e) = toV (N.head e)) ∨
    (N'.tail (toE e) = toV (N.head e) ∧ N'.head (toE e) = toV (N.tail e))
  /-- Sources correspond. -/
  source : N'.source = toV N.source
  /-- Sinks correspond. -/
  sink : N'.sink = toV N.sink

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype V'] [Fintype E'] [DecidableEq V']
  [DecidableEq E']

/-- The polynomial of a network does not change when the reference directions of some edges are reversed. -/
theorem pairPoly_reverse (N : Network V E) (S : E → Prop) [DecidablePred S] (ε : E → Bool) :
    (N.reverse S).pairPoly ε = N.pairPoly ε := by
  let s : E ⊕ V → ℤ[X] := Sum.elim (fun e => if S e then -1 else 1) (fun _ => 1)
  have hM : (N.reverse S).pairMatrix ε = Matrix.diagonal s * N.pairMatrix ε * Matrix.diagonal s := by
    refine Matrix.ext fun p q => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases p with e | v <;> rcases q with e' | v' <;>
      simp only [pairMatrix, system, reverse, Matrix.of_apply, s, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one]
    · by_cases he : e' = e
      · subst he
        split_ifs <;> ring
      · simp only [he, ↓reduceIte, mul_zero, zero_mul]
    · split_ifs <;> ring
    · by_cases hv : v = N.sink
      · simp only [hv, ↓reduceIte, zero_mul]
      · by_cases hS : S e' <;> simp only [hv, hS, ↓reduceIte] <;> ring
    · rfl
  have hs : (∏ p, s p) * ∏ p, s p = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p _ => ?_
    rcases p with e | v
    · by_cases hS : S e <;> simp [s, hS]
    · simp [s]
  rw [pairPoly, pairPoly, hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_right_comm, hs, one_mul]

/-- Networks that correspond up to the reference directions of their edges, with corresponding orientation vectors, have the same polynomial. -/
theorem UIso.pairPoly_eq {N : Network V E} {N' : Network V' E'} (U : UIso N N') {ε : E → Bool} {ε' : E' → Bool}
    (hε : ∀ e, ε' (U.toE e) = ε e) : N'.pairPoly ε' = N.pairPoly ε := by
  classical
  let S : E → Prop := fun e =>
    ¬(N'.tail (U.toE e) = U.toV (N.tail e) ∧ N'.head (U.toE e) = U.toV (N.head e))
  let I : Iso (N.reverse S) N' :=
    { toV := U.toV
      toE := U.toE
      tail := fun e => by
        by_cases hS : S e
        · rcases U.ends e with h | h
          · exact absurd h hS
          · simp only [reverse, hS, ↓reduceIte, h.1]
        · simp only [reverse, hS, ↓reduceIte, (not_not.mp hS).1]
      head := fun e => by
        by_cases hS : S e
        · rcases U.ends e with h | h
          · exact absurd h hS
          · simp only [reverse, hS, ↓reduceIte, h.2]
        · simp only [reverse, hS, ↓reduceIte, (not_not.mp hS).2]
      source := U.source
      sink := U.sink }
  rw [I.pairPoly_eq hε, pairPoly_reverse]

end Network

/-- A bijection that intertwines two permutations carries the cycles of one to the cycles of the other. -/
theorem sameCycle_map_iff {D D' : Type*} {f : Equiv.Perm D} {f' : Equiv.Perm D'} (π : D ≃ D')
    (h : ∀ d, π (f d) = f' (π d)) {a b : D} : f'.SameCycle (π a) (π b) ↔ f.SameCycle a b := by
  have hinv : ∀ d, π (f⁻¹ d) = f'⁻¹ (π d) := fun d => by
    rw [Equiv.Perm.eq_inv_iff_eq, ← h]
    simp
  have hpow : ∀ (i : ℤ) (d : D), π ((f ^ i) d) = (f' ^ i) (π d) := by
    intro i
    induction i using Int.induction_on with
    | zero => intro d; simp
    | succ i ih => intro d; rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, h]
    | pred i ih =>
      intro d
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, hinv]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, π.injective (by rw [hpow, hi])⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hpow, hi]⟩

/-- Induction along a cycle of a permutation of a finite set. -/
theorem sameCycle_induction {D : Type*} [Finite D] {f : Equiv.Perm D} {a b : D} (h : f.SameCycle a b)
    (P : D → Prop) (h0 : P a) (hs : ∀ d, P d → P (f d)) : P b := by
  have key : ∀ i : ℕ, P ((f ^ i) a) := by
    intro i
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hs _ ih
  obtain ⟨i, -, rfl⟩ := h.exists_pow_eq'
  exact key i

/-- The bijection between the cycles of two permutations that a bijection intertwines. -/
def cycleEquiv {D D' : Type*} {f : Equiv.Perm D} {f' : Equiv.Perm D'} (π : D ≃ D')
    (h : ∀ d, π (f d) = f' (π d)) :
    Quotient (Equiv.Perm.SameCycle.setoid f) ≃ Quotient (Equiv.Perm.SameCycle.setoid f') :=
  Quotient.congr π fun _ _ => (sameCycle_map_iff π h).symm

namespace CMap

variable {D D' : Type*}

/-- The vertex of a dart. -/
def vertex (M : CMap D) (d : D) : M.Vertex :=
  Quotient.mk _ d

/-- The edge of a dart. -/
def edge (M : CMap D) (d : D) : M.Edge :=
  Quotient.mk _ d

/-- The face of a dart. -/
def faceOf (M : CMap D) (d : D) : M.Face :=
  Quotient.mk _ d

theorem vertex_eq_iff (M : CMap D) {a b : D} : M.vertex a = M.vertex b ↔ M.σ.SameCycle a b :=
  Quotient.eq

theorem faceOf_eq_iff (M : CMap D) {a b : D} : M.faceOf a = M.faceOf b ↔ M.face.SameCycle a b :=
  Quotient.eq

theorem vertex_σ (M : CMap D) (d : D) : M.vertex (M.σ d) = M.vertex d :=
  M.vertex_eq_iff.mpr (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

theorem vertex_surjective (M : CMap D) : Function.Surjective M.vertex :=
  Quotient.mk_surjective

theorem edge_surjective (M : CMap D) : Function.Surjective M.edge :=
  Quotient.mk_surjective

/-- Two darts lie on the same edge when they are equal or exchanged by `α`. -/
theorem edge_eq_iff (M : CMap D) {a b : D} : M.edge a = M.edge b ↔ b = a ∨ b = M.α a := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ : M.α.SameCycle a b := Quotient.eq.mp h
    have hsq : M.α ^ (2 : ℤ) = 1 := by
      ext d
      rw [zpow_two, Equiv.Perm.mul_apply, M.α_invol, Equiv.Perm.one_apply]
    rcases Int.emod_two_eq_zero_or_one i with h0 | h1
    · left
      rw [← Int.mul_ediv_add_emod i 2, h0, add_zero, zpow_mul, hsq, one_zpow, Equiv.Perm.one_apply]
    · right
      rw [← Int.mul_ediv_add_emod i 2, h1, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · rfl
    · exact Quotient.eq.mpr (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))

theorem edge_α (M : CMap D) (d : D) : M.edge (M.α d) = M.edge d :=
  (M.edge_eq_iff.mpr (Or.inr rfl)).symm

/-- A dart of an edge. -/
noncomputable def Edge.dart {M : CMap D} (q : M.Edge) : D :=
  Quotient.out q

theorem edge_dart {M : CMap D} (q : M.Edge) : M.edge q.dart = q :=
  Quotient.out_eq q

/-- The edges other than that of the dart `r`. -/
def Tile (M : CMap D) (r : D) : Type _ :=
  {q : M.Edge // q ≠ M.edge r}

/-- The network of a map with the root `r`: the vertices of the map, the edges other than that of the root, the sink at the vertex of the root and the source at the other end of its edge. -/
noncomputable def net (M : CMap D) (r : D) : Network M.Vertex (M.Tile r) where
  tail q := M.vertex q.1.dart
  head q := M.vertex (M.α q.1.dart)
  source := M.vertex (M.α r)
  sink := M.vertex r

instance [Finite D] (M : CMap D) : Finite M.Vertex :=
  inferInstanceAs (Finite (Quotient _))

instance [Finite D] (M : CMap D) : Finite M.Edge :=
  inferInstanceAs (Finite (Quotient _))

instance [Finite D] (M : CMap D) : Finite M.Face :=
  inferInstanceAs (Finite (Quotient _))

instance [Finite D] (M : CMap D) (r : D) : Finite (M.Tile r) :=
  inferInstanceAs (Finite {q : M.Edge // q ≠ M.edge r})

noncomputable instance [Finite D] (M : CMap D) : Fintype M.Vertex :=
  Fintype.ofFinite _

noncomputable instance [Finite D] (M : CMap D) (r : D) : Fintype (M.Tile r) :=
  Fintype.ofFinite _

/-- Isomorphism of maps: a bijection of the darts that intertwines the two permutations. -/
structure Iso (M : CMap D) (M' : CMap D') where
  /-- The bijection between the darts. -/
  toFun : D ≃ D'
  /-- The rotations correspond. -/
  σ : ∀ d, toFun (M.σ d) = M'.σ (toFun d)
  /-- The involutions correspond. -/
  α : ∀ d, toFun (M.α d) = M'.α (toFun d)

namespace Iso

variable {M : CMap D} {M' : CMap D'}

/-- The inverse isomorphism. -/
def symm (I : Iso M M') : Iso M' M where
  toFun := I.toFun.symm
  σ d := by
    rw [Equiv.symm_apply_eq, I.σ, Equiv.apply_symm_apply]
  α d := by
    rw [Equiv.symm_apply_eq, I.α, Equiv.apply_symm_apply]

theorem face (I : Iso M M') (d : D) : I.toFun (M.face d) = M'.face (I.toFun d) := by
  simp only [CMap.face, Equiv.Perm.mul_apply, I.σ, I.α]

theorem σ_symm (I : Iso M M') (d : D) : I.toFun (M.σ.symm d) = M'.σ.symm (I.toFun d) := by
  rw [Equiv.eq_symm_apply, ← I.σ, Equiv.apply_symm_apply]

/-- The bijection between the vertices. -/
def vertexEquiv (I : Iso M M') : M.Vertex ≃ M'.Vertex :=
  cycleEquiv I.toFun I.σ

/-- The bijection between the edges. -/
def edgeEquiv (I : Iso M M') : M.Edge ≃ M'.Edge :=
  cycleEquiv I.toFun I.α

/-- The bijection between the faces. -/
def faceEquiv (I : Iso M M') : M.Face ≃ M'.Face :=
  cycleEquiv I.toFun I.face

theorem vertexEquiv_vertex (I : Iso M M') (d : D) : I.vertexEquiv (M.vertex d) = M'.vertex (I.toFun d) :=
  rfl

theorem edgeEquiv_edge (I : Iso M M') (d : D) : I.edgeEquiv (M.edge d) = M'.edge (I.toFun d) :=
  rfl

theorem connected (I : Iso M M') (h : M.Connected) : M'.Connected := by
  intro d d'
  obtain ⟨a, rfl⟩ := I.toFun.surjective d
  obtain ⟨b, rfl⟩ := I.toFun.surjective d'
  refine (h a b).lift I.toFun ?_
  rintro x y (rfl | rfl)
  · exact Or.inl (I.σ x)
  · exact Or.inr (I.α x)

theorem planar (I : Iso M M') (h : M.Planar) : M'.Planar := by
  refine ⟨I.connected h.1, ?_⟩
  rw [← Nat.card_congr I.vertexEquiv, ← Nat.card_congr I.faceEquiv, ← Nat.card_congr I.edgeEquiv]
  exact h.2

theorem loopless (I : Iso M M') (h : M.Loopless) : M'.Loopless := by
  intro d' hd
  obtain ⟨d, rfl⟩ := I.toFun.surjective d'
  rw [← I.α, sameCycle_map_iff I.toFun I.σ] at hd
  exact h d hd

theorem noCutVertex (I : Iso M M') (h : M.NoCutVertex) : M'.NoCutVertex := by
  intro u' d' e' hd he
  obtain ⟨u, rfl⟩ := I.toFun.surjective u'
  obtain ⟨d, rfl⟩ := I.toFun.surjective d'
  obtain ⟨e, rfl⟩ := I.toFun.surjective e'
  rw [sameCycle_map_iff I.toFun I.σ] at hd he
  refine (h u d e hd he).lift I.toFun ?_
  rintro x y (rfl | ⟨rfl, hy⟩)
  · exact Or.inl (I.σ x)
  · exact Or.inr ⟨I.α x, by rwa [sameCycle_map_iff I.toFun I.σ]⟩

/-- The bijection between the edges other than those of corresponding roots. -/
def tileEquiv (I : Iso M M') (r : D) : M.Tile r ≃ M'.Tile (I.toFun r) :=
  Equiv.subtypeEquiv I.edgeEquiv fun q => by
    rw [← I.edgeEquiv_edge, Ne, Ne, I.edgeEquiv.injective.eq_iff]

/-- The networks of isomorphic maps with corresponding roots correspond, up to the reference directions of their edges. -/
noncomputable def netUIso (I : Iso M M') (r : D) : Network.UIso (M.net r) (M'.net (I.toFun r)) where
  toV := I.vertexEquiv
  toE := I.tileEquiv r
  ends q := by
    have h1 : M'.edge (I.toFun q.1.dart) = M'.edge (I.tileEquiv r q).1.dart := by
      rw [edge_dart, ← I.edgeEquiv_edge, edge_dart]
      rfl
    rcases M'.edge_eq_iff.mp h1 with h2 | h2
    · left
      refine ⟨?_, ?_⟩
      · change M'.vertex (I.tileEquiv r q).1.dart = I.vertexEquiv (M.vertex q.1.dart)
        rw [h2, I.vertexEquiv_vertex]
      · change M'.vertex (M'.α (I.tileEquiv r q).1.dart) = I.vertexEquiv (M.vertex (M.α q.1.dart))
        rw [h2, I.vertexEquiv_vertex, I.α]
    · right
      refine ⟨?_, ?_⟩
      · change M'.vertex (I.tileEquiv r q).1.dart = I.vertexEquiv (M.vertex (M.α q.1.dart))
        rw [h2, I.vertexEquiv_vertex, I.α]
      · change M'.vertex (M'.α (I.tileEquiv r q).1.dart) = I.vertexEquiv (M.vertex q.1.dart)
        rw [h2, I.vertexEquiv_vertex, M'.α_invol]
  source := by
    change M'.vertex (M'.α (I.toFun r)) = I.vertexEquiv (M.vertex (M.α r))
    rw [I.vertexEquiv_vertex, I.α]
  sink := rfl

end Iso

open Classical in
/-- The proportions of a map with the root `r`: the real roots of the polynomials of its network for the orientation vectors in which the edge before the root, in the rotation at its vertex, is wide. -/
def rootSet [Finite D] (M : CMap D) (r : D) : Set ℝ :=
  {x | ∃ ε : M.Tile r → Bool, (∀ q : M.Tile r, q.1 = M.edge (M.σ.symm r) → ε q = false) ∧
    x ∈ ((M.net r).pairPoly ε).aroots ℝ}

/-- The proportions of a map with a root are proportions of every isomorphic map with the corresponding root. -/
theorem Iso.rootSet_subset [Finite D] [Finite D'] {M : CMap D} {M' : CMap D'} (I : Iso M M') (r : D) :
    M.rootSet r ⊆ M'.rootSet (I.toFun r) := by
  classical
  rintro x ⟨ε, hc, hx⟩
  refine ⟨fun q' => ε ((I.tileEquiv r).symm q'), fun q' hq' => hc _ ?_, ?_⟩
  · apply I.edgeEquiv.injective
    have h1 : I.edgeEquiv ((I.tileEquiv r).symm q').1 = q'.1 :=
      congrArg Subtype.val ((I.tileEquiv r).apply_symm_apply q')
    rw [h1, hq', I.edgeEquiv_edge, I.σ_symm]
  · rwa [(I.netUIso r).pairPoly_eq (ε := ε) fun e => congrArg ε ((I.tileEquiv r).symm_apply_apply e)]

end CMap

namespace RootedMap

variable {m : ℕ}

/-- The isomorphism of maps that underlies an isomorphism of rooted maps. -/
theorem Isomorphic.exists_iso {M M' : RootedMap m} (h : M.Isomorphic M') :
    ∃ I : CMap.Iso M.map M'.map, I.toFun M.root = M'.root := by
  obtain ⟨π, hσ, hα, hr⟩ := h
  exact ⟨⟨π, hσ, hα⟩, hr⟩

theorem Isomorphic.symm {M M' : RootedMap m} (h : M.Isomorphic M') : M'.Isomorphic M := by
  obtain ⟨I, hr⟩ := h.exists_iso
  exact ⟨I.symm.toFun, I.symm.σ, I.symm.α, by rw [← hr]; exact I.toFun.symm_apply_apply _⟩

/-- The edges of a rooted map other than that of the root. -/
def Tile (M : RootedMap m) : Type :=
  M.map.Tile M.root

noncomputable instance (M : RootedMap m) : Fintype M.Tile :=
  inferInstanceAs (Fintype (M.map.Tile M.root))

/-- The network of a rooted map. -/
noncomputable def net (M : RootedMap m) : Network M.map.Vertex M.Tile :=
  M.map.net M.root

open Classical in
/-- The polynomial of a rooted map with an orientation vector. -/
noncomputable def poly (M : RootedMap m) (ε : M.Tile → Bool) : Polynomial ℤ :=
  M.net.pairPoly ε

/-- The polynomials of isomorphic rooted maps correspond, by a bijection between their edges. -/
theorem Isomorphic.poly_eq {M M' : RootedMap m} (h : M.Isomorphic M') :
    ∃ f : M.Tile ≃ M'.Tile, ∀ ε : M.Tile → Bool, M'.poly (fun q => ε (f.symm q)) = M.poly ε := by
  classical
  obtain ⟨M', r', _, _, _⟩ := M'
  obtain ⟨π, hσ, hα, hr⟩ := h
  simp only at hr hσ hα
  subst hr
  let I : CMap.Iso M.map M' := ⟨π, hσ, hα⟩
  exact ⟨I.tileEquiv M.root, fun ε =>
    (I.netUIso M.root).pairPoly_eq fun e => congrArg ε ((I.tileEquiv M.root).symm_apply_apply e)⟩

/-- The proportions of a rooted map. -/
def rootSet (M : RootedMap m) : Set ℝ :=
  M.map.rootSet M.root

/-- Isomorphic rooted maps have the same proportions. -/
theorem Isomorphic.rootSet_eq {M M' : RootedMap m} (h : M.Isomorphic M') : M.rootSet = M'.rootSet := by
  have key : ∀ {M M' : RootedMap m}, M.Isomorphic M' → M.rootSet ⊆ M'.rootSet := by
    intro M M' h
    obtain ⟨I, hr⟩ := h.exists_iso
    rw [rootSet, rootSet, ← hr]
    exact I.rootSet_subset M.root
  exact Set.Subset.antisymm (key h) (key h.symm)

end RootedMap

/-- The proportions of a class of rooted maps. -/
def RootedMapClass.rootSet {m : ℕ} : RootedMapClass m → Set ℝ :=
  Quot.lift RootedMap.rootSet fun _ _ h => h.rootSet_eq

end Rectiling
