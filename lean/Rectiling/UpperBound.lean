-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.TilingMapPlanar
import Rectiling.Persistence

/-!
# The upper bound on the number of proportions

The map of a tiling with `n` tiles, rooted at the additional edge, is a rooted non-separable planar map with `n + 1` edges, and its network is that of the tiling.
A proportion with which the unit square can be cut into `n` similar rectangles is a root of the polynomial of such a map for an orientation vector in which the tile at the bottom left corner is wide, after a transposition if necessary; the polynomial depends only on the class of the rooted map.
Hence, given the enumeration of Tutte, the proportions are at most `n 2 ^ (n - 1)` times the number of rooted non-separable planar maps with `n + 1` edges, and the upper limit of the `n`-th roots of their number is at most `27 / 2`.
-/

namespace Rectiling

open Classical

/-- The orientation vectors on `n` tiles in which a given tile is wide are at most `2 ^ (n - 1)`. -/
theorem card_filter_false_le (n : ℕ) (e₀ : Fin n) :
    (Finset.univ.filter fun ε : Fin n → Bool => ε e₀ = false).card ≤ 2 ^ (n - 1) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun ε => ε e₀ = false)
  have h2 : (Finset.univ.filter fun ε : Fin n → Bool => ε e₀ = false).card ≤
      (Finset.univ.filter fun ε : Fin n → Bool => ¬ε e₀ = false).card := by
    refine Finset.card_le_card_of_injOn (fun ε => Function.update ε e₀ true) ?_ ?_
    · intro ε _
      simp
    · intro ε₁ h1 ε₂ h2 heq
      rw [Finset.mem_coe, Finset.mem_filter] at h1 h2
      funext i
      by_cases hi : i = e₀
      · rw [hi, h1.2, h2.2]
      · have := congrFun heq i
        simpa [Function.update_of_ne hi] using this
  have h3 : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  have h4 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos e₀).ne'
    rw [Nat.succ_sub_one, pow_succ, mul_comm]
  omega

namespace CMap

variable {D D' : Type*}

/-- The map carried to another set of darts by a bijection. -/
def map (M : CMap D) (f : D ≃ D') : CMap D' where
  σ := f.permCongr M.σ
  α := f.permCongr M.α
  α_invol d := by simp [Equiv.permCongr_apply, M.α_invol]
  α_ne d hd := M.α_ne (f.symm d) (f.eq_symm_apply.mpr hd)

/-- A map is isomorphic to the map carried to another set of darts. -/
def mapIso (M : CMap D) (f : D ≃ D') : Iso M (M.map f) where
  toFun := f
  σ d := by simp [map, Equiv.permCongr_apply]
  α d := by simp [map, Equiv.permCongr_apply]

end CMap

/-- The numbering of the darts of the map of a tiling with `n` tiles. -/
noncomputable def dartEquiv (n : ℕ) : Dart n ≃ Fin (2 * (n + 1)) :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Fintype.card_bool]
    ring)

instance (m : ℕ) : Finite (RootedMap m) := by
  refine Finite.of_injective (fun M : RootedMap m => (M.map.σ, M.map.α, M.root)) ?_
  rintro ⟨⟨σ, α, _, _⟩, r, _, _, _⟩ ⟨⟨σ', α', _, _⟩, r', _, _, _⟩ heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  rfl

instance (m : ℕ) : Finite (RootedMapClass m) :=
  inferInstanceAs (Finite (Quot _))

variable {W H : ℝ} {tl : List Rect} {M : CMap (Dart tl.length)}

local notation "Lx" e:max => Rect.x (List.get tl e)
local notation "Rx" e:max => (Rect.x (List.get tl e) + Rect.w (List.get tl e))
local notation "By" e:max => Rect.y (List.get tl e)
local notation "Ty" e:max => (Rect.y (List.get tl e) + Rect.h (List.get tl e))

namespace IsTilingMap

/-- The edge of a tile is not the additional edge. -/
theorem edge_ne (hM : IsTilingMap W H tl M) (e : Fin tl.length) :
    M.edge (some e, true) ≠ M.edge (none, false) := by
  intro hc
  rcases M.edge_eq_iff.mp hc with h1 | h1
  · exact absurd h1 (by simp)
  · rw [hM.alpha] at h1
    exact absurd h1 (by simp)

/-- The bijection between the tiles and the edges of the map other than the additional edge. -/
noncomputable def tileEquiv (hM : IsTilingMap W H tl M) : Fin tl.length ≃ M.Tile (none, false) :=
  Equiv.ofBijective (fun e => (Subtype.mk (M.edge (some e, true)) (hM.edge_ne e) : M.Tile (none, false)))
    ⟨by
      intro e e' heq
      rcases M.edge_eq_iff.mp (congrArg Subtype.val heq) with h1 | h1
      · simpa using h1.symm
      · rw [hM.alpha] at h1
        exact absurd h1 (by simp), by
      rintro ⟨E, hE⟩
      obtain ⟨d, rfl⟩ := M.edge_surjective E
      rcases d with ⟨_ | e, _ | _⟩
      · exact absurd rfl hE
      · exact absurd (M.edge_eq_iff.mpr (Or.inr (hM.alpha (none, true)).symm)) hE
      · exact ⟨e, Subtype.ext (M.edge_eq_iff.mpr (Or.inr (hM.alpha (some e, true)).symm))⟩
      · exact ⟨e, rfl⟩⟩

theorem tileEquiv_val (hM : IsTilingMap W H tl M) (e : Fin tl.length) :
    (hM.tileEquiv e).1 = M.edge (some e, true) :=
  rfl

/-- The network of the map of a tiling, rooted at the additional edge, is the network of the tiling up to the reference directions of the edges. -/
noncomputable def netUIso (hM : IsTilingMap W H tl M) : Network.UIso (tilingNet M) (M.net (none, false)) where
  toV := Equiv.refl _
  toE := hM.tileEquiv
  ends e := by
    have h1 : M.edge (some e, true) = M.edge (hM.tileEquiv e).1.dart := (CMap.edge_dart _).symm
    rcases M.edge_eq_iff.mp h1 with h2 | h2
    · left
      refine ⟨?_, ?_⟩
      · change M.vertex (hM.tileEquiv e).1.dart = M.vertex (some e, true)
        rw [h2]
      · change M.vertex (M.α (hM.tileEquiv e).1.dart) = M.vertex (some e, false)
        rw [h2, hM.alpha]
        rfl
    · right
      refine ⟨?_, ?_⟩
      · change M.vertex (hM.tileEquiv e).1.dart = M.vertex (some e, false)
        rw [h2, hM.alpha]
        rfl
      · change M.vertex (M.α (hM.tileEquiv e).1.dart) = M.vertex (some e, true)
        rw [h2, M.α_invol]
  source := by
    change M.vertex (M.α (none, false)) = M.vertex (none, true)
    rw [hM.alpha]
    rfl
  sink := rfl

/-- The bottom end of the tile at the bottom left corner is followed by the additional edge. -/
theorem σ_corner (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) {e₀ : Fin tl.length}
    (hx0 : Lx e₀ = 0) (hy0 : By e₀ = 0) : M.σ (some e₀, false) = (none, false) := by
  rcases hM.rotation.bot e₀ with ⟨a, -, -, ha2⟩ | ⟨a, -, ha1, -⟩ | ⟨ha, -, -⟩
  · linarith [(h.get_bounds a).1, (h.get_bounds a).2.2.1]
  · linarith [(h.get_bounds a).2.1, (h.get_bounds a).2.2.2.2.1]
  · exact ha

/-- The edge before the root, in the map of a tiling rooted at the additional edge, is the tile at the bottom left corner. -/
theorem corner_edge (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) {e₀ : Fin tl.length}
    (hx0 : Lx e₀ = 0) (hy0 : By e₀ = 0) : (hM.tileEquiv e₀).1 = M.edge (M.σ.symm (none, false)) := by
  rw [(Equiv.symm_apply_eq M.σ).mpr (hM.σ_corner h hx0 hy0).symm]
  exact M.edge_eq_iff.mpr (Or.inr (hM.alpha (some e₀, true)).symm)

/-- The proportion of a similar tiling of the unit square in which the tile at the bottom left corner is wide is a proportion of the map of the tiling, rooted at the additional edge. -/
theorem mem_rootSet {x : ℝ} (hM : IsTilingMap 1 1 tl M) (hs : IsSimilarTiling x (Rect.main 1 1) tl)
    {e₀ : Fin tl.length} (hx0 : Lx e₀ = 0) (hy0 : By e₀ = 0) (hwide : (tl.get e₀).w = x * (tl.get e₀).h) :
    x ∈ M.rootSet (none, false) := by
  refine ⟨fun q => narrowVector x tl (hM.tileEquiv.symm q), fun q hq => ?_, ?_⟩
  · have h1 : q = hM.tileEquiv e₀ := Subtype.ext (hq.trans (hM.corner_edge hs.toIsTiling hx0 hy0).symm)
    change narrowVector x tl (hM.tileEquiv.symm q) = false
    rw [h1, Equiv.symm_apply_apply]
    simp only [narrowVector, hwide, not_true_eq_false, decide_false]
  · rw [Polynomial.mem_aroots, hM.netUIso.pairPoly_eq (ε := narrowVector x tl) fun e =>
      congrArg _ (hM.tileEquiv.symm_apply_apply e)]
    exact ⟨(hM.tilingNet_proper hs.toIsTiling one_pos).pairPoly_ne_zero _, hs.aeval_tilingNet hM⟩

/-- The proportions of the map of a tiling with `n` tiles, rooted at the additional edge, are at most `n 2 ^ (n - 1)`. -/
theorem rootSet_finite_and_ncard_le (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl)
    (hW : 0 < W) (hH : 0 < H) :
    (M.rootSet (none, false)).Finite ∧ (M.rootSet (none, false)).ncard ≤ tl.length * 2 ^ (tl.length - 1) := by
  obtain ⟨e₀, hx0, hy0⟩ := h.exists_bottom_left hW hH
  let S := Finset.univ.filter fun ε : Fin tl.length → Bool => ε e₀ = false
  let T : Finset ℝ := S.biUnion fun ε => (((tilingNet M).pairPoly ε).aroots ℝ).toFinset
  have hsub : M.rootSet (none, false) ⊆ ↑T := by
    rintro x ⟨εq, hc, hx⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨fun e => εq (hM.tileEquiv e), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hc _ (hM.corner_edge h hx0 hy0)⟩
    · rw [Multiset.mem_toFinset, ← hM.netUIso.pairPoly_eq (ε := fun e => εq (hM.tileEquiv e)) (ε' := εq) fun e => rfl]
      exact hx
  have hcard : T.card ≤ tl.length * 2 ^ (tl.length - 1) := by
    calc T.card ≤ ∑ ε ∈ S, (((tilingNet M).pairPoly ε).aroots ℝ).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _ε ∈ S, tl.length :=
        Finset.sum_le_sum fun ε _ => by simpa using (tilingNet M).card_aroots_pairPoly_le ε
      _ = S.card * tl.length := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ (tl.length - 1) * tl.length := Nat.mul_le_mul_right _ (card_filter_false_le _ e₀)
      _ = tl.length * 2 ^ (tl.length - 1) := mul_comm _ _
  exact ⟨T.finite_toSet.subset hsub,
    (Set.ncard_le_ncard hsub T.finite_toSet).trans (by rwa [Set.ncard_coe_finset])⟩

/-- The map of a tiling with `n` tiles, rooted at the additional edge on the bottom side, as a rooted non-separable planar map with `n + 1` edges. -/
noncomputable def rooted (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hW : 0 < W)
    (hH : 0 < H) : RootedMap (tl.length + 1) where
  map := M.map (dartEquiv tl.length)
  root := dartEquiv tl.length (none, false)
  planar := (M.mapIso _).planar (hM.planar h hW hH)
  loopless := (M.mapIso _).loopless (hM.loopless h hH)
  noCutVertex := (M.mapIso _).noCutVertex (hM.noCutVertex h)

/-- The proportions of the rooted map of a tiling are those of the map on the darts of the tiling. -/
theorem rooted_rootSet (hM : IsTilingMap W H tl M) (h : IsTiling (Rect.main W H) tl) (hW : 0 < W)
    (hH : 0 < H) : (hM.rooted h hW hH).rootSet = M.rootSet (none, false) := by
  refine Set.Subset.antisymm ?_ ((M.mapIso (dartEquiv tl.length)).rootSet_subset (none, false))
  have h1 := (M.mapIso (dartEquiv tl.length)).symm.rootSet_subset (dartEquiv tl.length (none, false))
  have h2 : (M.mapIso (dartEquiv tl.length)).symm.toFun (dartEquiv tl.length (none, false)) = (none, false) :=
    (dartEquiv tl.length).symm_apply_apply _
  rw [h2] at h1
  exact h1

end IsTilingMap

/-- A proportion with which the unit square can be cut into `n` similar rectangles serves for a tiling in which the tile at the bottom left corner is wide. -/
theorem Achievable.exists_wide_corner {n : ℕ} {x : ℝ} (hx : Achievable n x) :
    ∃ tl : List Rect, tl.length = n ∧ IsSimilarTiling x (Rect.main 1 1) tl ∧
      ∃ e₀ : Fin tl.length, (tl.get e₀).x = 0 ∧ (tl.get e₀).y = 0 ∧ (tl.get e₀).w = x * (tl.get e₀).h := by
  obtain ⟨tl, rfl, hs⟩ := hx
  obtain ⟨e₀, h1, h2⟩ := hs.toIsTiling.exists_bottom_left one_pos one_pos
  by_cases hw : (tl.get e₀).w = x * (tl.get e₀).h
  · exact ⟨tl, rfl, hs, e₀, h1, h2, hw⟩
  · have ht : (tl.get e₀).h = x * (tl.get e₀).w := (hs.proportion _ (List.get_mem tl e₀)).resolve_left hw
    refine ⟨tl.map Rect.transpose, by simp, hs.transpose, ⟨e₀.1, by simp⟩, ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, Rect.transpose]
    simp only [List.get_eq_getElem] at h1 h2 ht
    exact ⟨h2, h1, ht⟩

/-- A proportion with which the unit square can be cut into `n` similar rectangles is a proportion of a class of rooted non-separable planar maps with `n + 1` edges, which has at most `n 2 ^ (n - 1)` proportions. -/
theorem Achievable.exists_rootedMapClass {n : ℕ} {x : ℝ} (hx : Achievable n x) :
    ∃ c : RootedMapClass (n + 1), c.rootSet.Finite ∧ c.rootSet.ncard ≤ n * 2 ^ (n - 1) ∧ x ∈ c.rootSet := by
  obtain ⟨tl, rfl, hs, e₀, hx0, hy0, hwide⟩ := hx.exists_wide_corner
  have h := hs.toIsTiling
  have hM := tilingMap_isTilingMap h one_pos one_pos
  have hr : RootedMapClass.rootSet (Quot.mk _ (hM.rooted h one_pos one_pos)) =
      (tilingMap h one_pos one_pos).rootSet (none, false) := hM.rooted_rootSet h one_pos one_pos
  refine ⟨Quot.mk _ (hM.rooted h one_pos one_pos), ?_, ?_, ?_⟩
  · rw [hr]
    exact (hM.rootSet_finite_and_ncard_le h one_pos one_pos).1
  · rw [hr]
    exact (hM.rootSet_finite_and_ncard_le h one_pos one_pos).2
  · rw [hr]
    exact hM.mem_rootSet hs hx0 hy0 hwide

/-- Given the enumeration of Tutte, the number of proportions with which the unit square can be cut into `n ≥ 1` similar rectangles is at most `n 2 ^ (n - 1)` times the number `2 (3n)! / ((2n + 1)! (n + 1)!)` of rooted non-separable planar maps with `n + 1` edges. -/
theorem ncard_achievable_le_tutte (tutte : TutteEnumeration) {n : ℕ} (hn : 1 ≤ n) :
    {x : ℝ | Achievable n x}.ncard ≤ n * 2 ^ (n - 1) * tutteM n := by
  let _ : Fintype (RootedMapClass (n + 1)) := Fintype.ofFinite _
  let g : RootedMapClass (n + 1) → Set ℝ := fun c =>
    if c.rootSet.Finite ∧ c.rootSet.ncard ≤ n * 2 ^ (n - 1) then c.rootSet else ∅
  have hg : ∀ c, (g c).Finite ∧ (g c).ncard ≤ n * 2 ^ (n - 1) := by
    intro c
    by_cases hc : c.rootSet.Finite ∧ c.rootSet.ncard ≤ n * 2 ^ (n - 1)
    · simp only [g, hc, and_self, ↓reduceIte]
    · simp only [g, hc, ↓reduceIte, Set.finite_empty, Set.ncard_empty, zero_le, and_self]
  have hsub : {x : ℝ | Achievable n x} ⊆ ↑(Finset.univ.biUnion fun c => (hg c).1.toFinset) := by
    intro x hx
    obtain ⟨c, hfin, hcard, hxc⟩ := Achievable.exists_rootedMapClass hx
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨c, Finset.mem_univ _, (hg c).1.mem_toFinset.mpr ?_⟩
    simp only [g, hfin, hcard, and_self, ↓reduceIte]
    exact hxc
  calc {x : ℝ | Achievable n x}.ncard
      ≤ (Finset.univ.biUnion fun c => (hg c).1.toFinset).card := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ ∑ c : RootedMapClass (n + 1), ((hg c).1.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _c : RootedMapClass (n + 1), n * 2 ^ (n - 1) := Finset.sum_le_sum fun c _ => by
        rw [← Set.ncard_eq_toFinset_card _ (hg c).1]
        exact (hg c).2
    _ = n * 2 ^ (n - 1) * tutteM n := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, tutte.card_eq_tutteM hn, smul_eq_mul,
        mul_comm]

/-- Given the enumeration of Tutte, the upper limit of the `n`-th roots of the number of proportions with which the unit square can be cut into `n` similar rectangles is at most `27 / 2`. -/
theorem limsup_achievable_le (tutte : TutteEnumeration) :
    Filter.limsup (fun n : ℕ => ({x : ℝ | Achievable n x}.ncard : ℝ) ^ (1 / (n : ℝ))) Filter.atTop ≤ 27 / 2 :=
  limsup_le_of_le_tutteM (a := fun n => {x : ℝ | Achievable n x}.ncard) fun _ hn =>
    ncard_achievable_le_tutte tutte hn

end Rectiling
