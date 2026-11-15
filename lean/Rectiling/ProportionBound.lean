-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.TilingNetwork
import Rectiling.Persistence

/-!
# Finiteness of the set of proportions

Isomorphisms of networks, under which the polynomial of a network with an orientation vector is invariant, and the classes of networks with `n` edges and an orientation vector up to isomorphism.
The number of proportions with which the unit square can be cut into `n` similar rectangles is at most `n` times the number of these classes; in particular it is finite.
-/

namespace Rectiling

namespace Network

variable {V E V' E' : Type*}

/-- Isomorphism of networks: bijections between the vertices and between the edges that respect tails, heads and poles. -/
structure Iso (N : Network V E) (N' : Network V' E') where
  /-- The bijection between the vertices. -/
  toV : V ≃ V'
  /-- The bijection between the edges. -/
  toE : E ≃ E'
  /-- Tails correspond. -/
  tail : ∀ e, N'.tail (toE e) = toV (N.tail e)
  /-- Heads correspond. -/
  head : ∀ e, N'.head (toE e) = toV (N.head e)
  /-- Sources correspond. -/
  source : N'.source = toV N.source
  /-- Sinks correspond. -/
  sink : N'.sink = toV N.sink

/-- A network isomorphic to one with distinct poles, no loop and a connected graph has the same properties. -/
theorem Iso.proper {N : Network V E} {N' : Network V' E'} (I : Iso N N') (hN : N.Proper) : N'.Proper where
  source_ne_sink h := by
    rw [I.source, I.sink] at h
    exact hN.source_ne_sink (I.toV.injective h)
  loopless e' h := by
    obtain ⟨e, rfl⟩ := I.toE.surjective e'
    rw [I.tail, I.head] at h
    exact hN.loopless e (I.toV.injective h)
  connected v' := by
    obtain ⟨v, rfl⟩ := I.toV.surjective v'
    rw [I.sink]
    refine (hN.connected v).lift I.toV ?_
    rintro a b ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨I.toE e, Or.inl ⟨I.tail e, I.head e⟩⟩
    · exact ⟨I.toE e, Or.inr ⟨I.tail e, I.head e⟩⟩

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype V'] [Fintype E'] [DecidableEq V']
  [DecidableEq E']

/-- Isomorphic networks with corresponding orientation vectors have the same polynomial. -/
theorem Iso.pairPoly_eq {N : Network V E} {N' : Network V' E'} (I : Iso N N') {ε : E → Bool} {ε' : E' → Bool}
    (hε : ∀ e, ε' (I.toE e) = ε e) : N'.pairPoly ε' = N.pairPoly ε := by
  have hM : N.pairMatrix ε =
      (N'.pairMatrix ε').submatrix (Equiv.sumCongr I.toE I.toV) (Equiv.sumCongr I.toE I.toV) := by
    ext (p | p) (q | q) <;>
      simp [pairMatrix, system, I.tail, I.head, I.source, I.sink, hε]
  rw [pairPoly, pairPoly, hM, Matrix.det_submatrix_equiv_self]

end Network

/-- Network with `n` edges, with distinct poles, no loop and a connected graph, on vertices numbered from zero, together with an orientation vector. -/
structure Pair (n : ℕ) where
  /-- The number of vertices. -/
  order : Fin (n + 2)
  /-- The network. -/
  net : Network (Fin order) (Fin n)
  /-- The poles are distinct, no edge is a loop, and the graph is connected. -/
  proper : net.Proper
  /-- The orientation vector. -/
  tall : Fin n → Bool

instance (n : ℕ) : Finite (Pair n) := by
  refine Finite.of_injective
    (β := Σ k : Fin (n + 2), ((Fin n → Fin k) × (Fin n → Fin k) × Fin k × Fin k) × (Fin n → Bool))
    (fun p => ⟨p.order, (p.net.tail, p.net.head, p.net.source, p.net.sink), p.tall⟩) ?_
  rintro ⟨k, ⟨t, h, s, si⟩, _, ε⟩ ⟨k', ⟨t', h', s', si'⟩, _, ε'⟩ heq
  simp only [Sigma.mk.injEq] at heq
  obtain ⟨rfl, heq⟩ := heq
  simp only [heq_eq_eq, Prod.mk.injEq] at heq
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := heq
  rfl

/-- Two pairs are isomorphic when their networks are, by an isomorphism under which the orientation vectors correspond. -/
def Pair.Isomorphic {n : ℕ} (p q : Pair n) : Prop :=
  ∃ I : Network.Iso p.net q.net, ∀ e, q.tall (I.toE e) = p.tall e

/-- The classes of pairs with `n` edges up to isomorphism. -/
def PairClass (n : ℕ) : Type :=
  Quot (Pair.Isomorphic (n := n))

instance (n : ℕ) : Finite (PairClass n) :=
  inferInstanceAs (Finite (Quot _))

/-- The polynomial of a class of pairs. -/
noncomputable def PairClass.poly {n : ℕ} : PairClass n → Polynomial ℤ :=
  Quot.lift (fun p => p.net.pairPoly p.tall) fun _ _ ⟨I, hI⟩ => (I.pairPoly_eq hI).symm

/-- The polynomial of a class of pairs with `n` edges has at most `n` real roots. -/
theorem PairClass.card_aroots_le {n : ℕ} (c : PairClass n) : ((c.poly).aroots ℝ).toFinset.card ≤ n := by
  induction c using Quot.inductionOn with
  | _ p =>
    exact (show ((p.net.pairPoly p.tall).aroots ℝ).toFinset.card ≤ n by
      simpa using p.net.card_aroots_pairPoly_le p.tall)

/-- Every proportion with which the unit square can be cut into `n` similar rectangles is a root of the polynomial of a class of pairs with `n` edges. -/
theorem Achievable.exists_class {n : ℕ} {x : ℝ} (h : Achievable n x) :
    ∃ c : PairClass n, x ∈ (c.poly).aroots ℝ := by
  classical
  obtain ⟨tl, rfl, hs⟩ := h
  have hproper := hs.toIsTiling.heightNetwork_proper one_pos one_pos
  have hcard : Fintype.card {c : ℝ // c ∈ levels tl} < tl.length + 2 := by
    rw [Fintype.card_coe]
    exact Nat.lt_succ_of_le (card_levels_le tl)
  let f := Fintype.equivFin {c : ℝ // c ∈ levels tl}
  let N' : Network (Fin (Fintype.card {c : ℝ // c ∈ levels tl})) (Fin tl.length) :=
    ⟨fun e => f ((heightNetwork 1 tl).tail e), fun e => f ((heightNetwork 1 tl).head e),
      f (heightNetwork 1 tl).source, f (heightNetwork 1 tl).sink⟩
  let I : Network.Iso (heightNetwork 1 tl) N' :=
    ⟨f, Equiv.refl _, fun _ => rfl, fun _ => rfl, rfl, rfl⟩
  let p : Pair tl.length := ⟨⟨_, hcard⟩, N', I.proper hproper, tallVector x tl⟩
  refine ⟨Quot.mk _ p, ?_⟩
  have hp : PairClass.poly (Quot.mk _ p) = (heightNetwork 1 tl).pairPoly (tallVector x tl) :=
    I.pairPoly_eq fun _ => rfl
  rw [hp, Polynomial.mem_aroots]
  exact ⟨hproper.pairPoly_ne_zero _, hs.aeval_pairPoly⟩

/-- The number of proportions with which the unit square can be cut into `n` similar rectangles is at most `n` times the number of classes of pairs with `n` edges, and the set of these proportions is finite. -/
theorem finite_achievable_and_ncard_le (n : ℕ) :
    {x : ℝ | Achievable n x}.Finite ∧ {x : ℝ | Achievable n x}.ncard ≤ n * Nat.card (PairClass n) := by
  classical
  let _ : Fintype (PairClass n) := Fintype.ofFinite _
  have hsub : {x : ℝ | Achievable n x} ⊆
      ↑(Finset.univ.biUnion fun c : PairClass n => ((c.poly).aroots ℝ).toFinset) := by
    intro x hx
    obtain ⟨c, hc⟩ := Achievable.exists_class hx
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Finset.mem_coe, Multiset.mem_toFinset]
    exact ⟨c, hc⟩
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc {x : ℝ | Achievable n x}.ncard
      ≤ (Finset.univ.biUnion fun c : PairClass n => ((c.poly).aroots ℝ).toFinset).card := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ ∑ c : PairClass n, ((c.poly).aroots ℝ).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _c : PairClass n, n := Finset.sum_le_sum fun c _ => c.card_aroots_le
    _ = n * Nat.card (PairClass n) := by
      rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]

/-- The set of proportions with which the unit square can be cut into `n` similar rectangles is finite. -/
theorem finite_achievable (n : ℕ) : {x : ℝ | Achievable n x}.Finite :=
  (finite_achievable_and_ncard_le n).1

/-- The number of proportions with which the unit square can be cut into `n` similar rectangles is at most `n` times the number of classes of pairs with `n` edges. -/
theorem ncard_achievable_le (n : ℕ) : {x : ℝ | Achievable n x}.ncard ≤ n * Nat.card (PairClass n) :=
  (finite_achievable_and_ncard_le n).2

end Rectiling
