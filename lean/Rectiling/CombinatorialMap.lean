-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Growth

/-!
# Combinatorial maps and the enumeration of Tutte

Maps on a surface as pairs of permutations of a finite set of darts, planar maps by the characteristic of Euler, non-separable maps, rooted maps up to isomorphism, and the statement of the theorem of Tutte on the number of rooted non-separable planar maps.
The theorem is stated and not proved.
-/

namespace Rectiling

/-- Combinatorial map: the darts are the ends of the edges, `σ` sends a dart to the next dart around its vertex, and `α` exchanges the two ends of an edge. -/
structure CMap (D : Type*) where
  /-- The next dart around the vertex. -/
  σ : Equiv.Perm D
  /-- The other end of the edge. -/
  α : Equiv.Perm D
  /-- The other end of the other end is the dart. -/
  α_invol : ∀ d, α (α d) = d
  /-- The two ends of an edge are distinct. -/
  α_ne : ∀ d, α d ≠ d

namespace CMap

variable {D : Type*}

/-- The permutation whose cycles are the faces. -/
def face (M : CMap D) : Equiv.Perm D :=
  M.σ * M.α

/-- The vertices: the cycles of `σ`. -/
def Vertex (M : CMap D) : Type _ :=
  Quotient (Equiv.Perm.SameCycle.setoid M.σ)

/-- The edges: the cycles of `α`. -/
def Edge (M : CMap D) : Type _ :=
  Quotient (Equiv.Perm.SameCycle.setoid M.α)

/-- The faces: the cycles of the face permutation. -/
def Face (M : CMap D) : Type _ :=
  Quotient (Equiv.Perm.SameCycle.setoid M.face)

/-- Every dart is reached from every other by steps of `σ` and `α`. -/
def Connected (M : CMap D) : Prop :=
  ∀ d d', Relation.ReflTransGen (fun a b => b = M.σ a ∨ b = M.α a) d d'

/-- Connected map of genus zero: the numbers of vertices, edges and faces satisfy the formula of Euler for the sphere. -/
def Planar (M : CMap D) : Prop :=
  M.Connected ∧ Nat.card M.Vertex + Nat.card M.Face = Nat.card M.Edge + 2

/-- No edge has both ends at the same vertex. -/
def Loopless (M : CMap D) : Prop :=
  ∀ d, ¬M.σ.SameCycle d (M.α d)

/-- The removal of any vertex leaves the map connected: any two darts away from the vertex of `u` are joined by steps of `σ` and by steps of `α` that do not arrive at that vertex. -/
def NoCutVertex (M : CMap D) : Prop :=
  ∀ u d d', ¬M.σ.SameCycle u d → ¬M.σ.SameCycle u d' →
    Relation.ReflTransGen (fun a b => b = M.σ a ∨ (b = M.α a ∧ ¬M.σ.SameCycle u b)) d d'

end CMap

/-- Rooted non-separable planar map with `m` edges, on darts numbered from zero. -/
structure RootedMap (m : ℕ) where
  /-- The map. -/
  map : CMap (Fin (2 * m))
  /-- The root. -/
  root : Fin (2 * m)
  /-- The map is connected and of genus zero. -/
  planar : map.Planar
  /-- The map has no loop. -/
  loopless : map.Loopless
  /-- The map has no vertex whose removal disconnects it. -/
  noCutVertex : map.NoCutVertex

/-- Two rooted maps are isomorphic when a bijection of the darts carries the permutations and the root of one to those of the other. -/
def RootedMap.Isomorphic {m : ℕ} (M M' : RootedMap m) : Prop :=
  ∃ π : Equiv.Perm (Fin (2 * m)), (∀ d, π (M.map.σ d) = M'.map.σ (π d)) ∧
    (∀ d, π (M.map.α d) = M'.map.α (π d)) ∧ π M.root = M'.root

/-- The rooted non-separable planar maps with `m` edges up to isomorphism. -/
def RootedMapClass (m : ℕ) : Type :=
  Quot (RootedMap.Isomorphic (m := m))

/-- The theorem of Tutte: the number of rooted non-separable planar maps with `m ≥ 2` edges is `2 (3m - 3)! / (m! (2m - 1)!)`. -/
def TutteEnumeration : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    Nat.card (RootedMapClass m) = 2 * (3 * m - 3).factorial / (m.factorial * (2 * m - 1).factorial)

/-- Under the theorem of Tutte, the number of rooted non-separable planar maps with `n + 1 ≥ 2` edges is `2 (3n)! / ((2n + 1)! (n + 1)!)`. -/
theorem TutteEnumeration.card_eq_tutteM (tutte : TutteEnumeration) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (RootedMapClass (n + 1)) = tutteM n := by
  rw [tutte (n + 1) (by omega), tutteM]
  have h1 : 3 * (n + 1) - 3 = 3 * n := by omega
  have h2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [h1, h2, mul_comm (n + 1).factorial]

end Rectiling
