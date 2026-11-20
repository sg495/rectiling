-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Counts
import Rectiling.TilingCount

/-!
# Finiteness of the sets counted and the inequalities between the counts

The sets of tilings, of tilings by squares, of tilings of proportion greater than one, of classes under symmetry, of bags and of proportions are finite.
The parity of the number of tilings and the strict inequality between the numbers of proportions and of bags, without a hypothesis of finiteness.
The inequalities between the numbers of proportions, of bags, of classes and of tilings, the last of which rests on an orbit having at most eight elements.
The two notions of a point at which four tiles meet, for sets and for lists of rectangles, agree on tilings.
-/

namespace Rectiling

/-! ## Finiteness -/

/-- The unit square has finitely many similar tilings with `n` tiles. -/
theorem finite_similarTilingFinsets (n : ℕ) : (SimilarTilings n).Finite := by
  refine ((finite_similarTilings n).image List.toFinset).subset ?_
  intro T hT
  obtain ⟨l, x, h1, h2, h3⟩ := mem_similarTilings_iff.mp hT
  exact ⟨l, ⟨h2, x, h3⟩, h1⟩

theorem squareTilings_subset (n : ℕ) : SquareTilings n ⊆ SimilarTilings n := by
  rw [similarTilings_eq_union]
  exact Set.subset_union_left

theorem oblongTilings_subset (n : ℕ) : OblongTilings n ⊆ SimilarTilings n := by
  rw [similarTilings_eq_union]
  exact Set.subset_union_right

/-- The unit square has finitely many tilings by `n` squares. -/
theorem finite_squareTilings (n : ℕ) : (SquareTilings n).Finite :=
  (finite_similarTilingFinsets n).subset (squareTilings_subset n)

/-- The unit square has finitely many similar tilings with `n` tiles of proportion greater than one. -/
theorem finite_oblongTilings (n : ℕ) : (OblongTilings n).Finite :=
  (finite_similarTilingFinsets n).subset (oblongTilings_subset n)

/-- The similar tilings of the unit square with `n` tiles fall into finitely many classes under symmetry. -/
theorem finite_classes (n : ℕ) : (Classes n).Finite :=
  (finite_similarTilingFinsets n).image orbit

/-- The similar tilings of the unit square with `n` tiles have finitely many proportions. -/
theorem finite_proportions (n : ℕ) : (Proportions n).Finite :=
  (finite_achievable n).subset fun _ hx => mem_proportions_iff.mp hx

/-- The similar tilings of the unit square with `n` tiles have finitely many bags. -/
theorem finite_bags (n : ℕ) : (Bags n).Finite := by
  refine (((finite_proportions n).prod (finite_similarTilingFinsets n)).image
    fun p : ℝ × Finset Rect => (p.1, p.2.val.map Rect.short)).subset ?_
  rintro b ⟨x, T, hn, h, rfl⟩
  exact ⟨(x, T), ⟨⟨T, hn, h⟩, hn, x, h⟩, rfl⟩

/-! ## The statements on cardinalities, without hypotheses of finiteness -/

/-- The number of similar tilings of the unit square with `n` tiles of proportion greater than one is even. -/
theorem even_ncard_oblongTilings' (n : ℕ) : Even (OblongTilings n).ncard :=
  even_ncard_oblongTilings n (finite_oblongTilings n)

/-- **Parity of the number of tilings.** The number of similar tilings of the unit square with `n` tiles has the parity of the number of tilings of the unit square by `n` squares. -/
theorem parity_ncard_similarTilings (n : ℕ) :
    (SimilarTilings n).ncard % 2 = (SquareTilings n).ncard % 2 :=
  ncard_similarTilings_mod_two n (finite_similarTilingFinsets n)

/-- **More bags than proportions.** For every `n ≥ 6`, the number of bags of the similar tilings of the unit square with `n` tiles is greater than the number of their proportions. -/
theorem ncard_proportions_lt_ncard_bags' (n : ℕ) (hn : 6 ≤ n) : (Proportions n).ncard < (Bags n).ncard :=
  ncard_proportions_lt_ncard_bags n hn (finite_bags n)

/-! ## Orbits have at most eight elements -/

namespace Rect

/-- The number of quarter turns of a symmetry matters only modulo four. -/
theorem sym_mod_four (e : Bool) (k : ℕ) : sym e (k % 4) = sym e k := by
  funext r
  conv_rhs => rw [← Nat.div_add_mod k 4]
  simp only [sym]
  rw [Function.iterate_add_apply, iterate_four_mul_rot]

theorem short_rot (r : Rect) : r.rot.short = r.short :=
  min_comm _ _

theorem short_transpose (r : Rect) : r.transpose.short = r.short :=
  min_comm _ _

theorem short_iterate_rot (k : ℕ) (r : Rect) : (rot^[k] r).short = r.short := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, short_rot]

/-- A symmetry of the square preserves the short side of a rectangle. -/
theorem short_sym (e : Bool) (k : ℕ) (r : Rect) : (sym e k r).short = r.short := by
  cases e
  · exact short_iterate_rot k r
  · exact (short_iterate_rot k _).trans (short_transpose r)

end Rect

/-- The orbit of a set of rectangles is the set of its images under an optional transposition followed by at most three quarter turns. -/
theorem orbit_eq_range (T : Finset Rect) :
    orbit T = Set.range fun p : Bool × Fin 4 => T.image (Rect.sym p.1 p.2) := by
  ext T'
  constructor
  · rintro ⟨e, k, rfl⟩
    exact ⟨(e, ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩), by simp only [Rect.sym_mod_four]⟩
  · rintro ⟨⟨e, k⟩, rfl⟩
    exact ⟨e, k, rfl⟩

/-- **Eight symmetries.** The orbit of a set of rectangles under the symmetries of the square has at most eight elements. -/
theorem ncard_orbit_le (T : Finset Rect) : (orbit T).Finite ∧ (orbit T).ncard ≤ 8 := by
  rw [orbit_eq_range, ← Set.image_univ]
  refine ⟨Set.finite_univ.image _, (Set.ncard_image_le Set.finite_univ).trans ?_⟩
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  simp

/-! ## The bag is constant on orbits -/

/-- A symmetry of the square preserves the multiset of the short sides of a set of rectangles. -/
theorem map_short_image_sym (T : Finset Rect) (e : Bool) (k : ℕ) :
    (T.image (Rect.sym e k)).val.map Rect.short = T.val.map Rect.short := by
  rw [Finset.image_val_of_injOn (Rect.sym_injective e k).injOn, Multiset.map_map]
  exact Multiset.map_congr rfl fun r _ => Rect.short_sym e k r

/-- **Symmetric tilings have the same bag.** Two similar tilings of the unit square in the same orbit have the same proportion and the same multiset of short sides. -/
theorem bag_eq_of_mem_orbit {x x' : ℝ} {T T' : Finset Rect} (h : IsSimilarSetTiling x (Rect.main 1 1) T)
    (h' : IsSimilarSetTiling x' (Rect.main 1 1) T') (ho : T' ∈ orbit T) :
    x' = x ∧ T'.val.map Rect.short = T.val.map Rect.short := by
  obtain ⟨e, k, rfl⟩ := ho
  exact ⟨h'.proportion_unique nondegenerate_main_one (h.sym e k), map_short_image_sym T e k⟩

/-! ## The inequalities between the counts -/

/-- There are at most as many proportions as bags. -/
theorem ncard_proportions_le_ncard_bags (n : ℕ) : (Proportions n).ncard ≤ (Bags n).ncard := by
  rw [← image_fst_bags]
  exact Set.ncard_image_le (finite_bags n)

/-- There are at most as many bags as classes under symmetry. -/
theorem ncard_bags_le_ncard_classes (n : ℕ) : (Bags n).ncard ≤ (Classes n).ncard := by
  have key : ∀ b ∈ Bags n, ∃ T : Finset Rect, T.card = n ∧ IsSimilarSetTiling b.1 (Rect.main 1 1) T ∧
      b.2 = T.val.map Rect.short := by
    rintro b ⟨x, T, hn, h, rfl⟩
    exact ⟨T, hn, h, rfl⟩
  choose! F hF using key
  refine Set.ncard_le_ncard_of_injOn (fun b => orbit (F b)) ?_ ?_ (finite_classes n)
  · intro b hb
    exact ⟨F b, ⟨(hF b hb).1, b.1, (hF b hb).2.1⟩, rfl⟩
  · intro b hb b' hb' he
    have hmem : F b' ∈ orbit (F b) := by
      rw [show orbit (F b) = orbit (F b') from he]
      exact mem_orbit_self _
    obtain ⟨h1, h2⟩ := bag_eq_of_mem_orbit (hF b hb).2.1 (hF b' hb').2.1 hmem
    exact Prod.ext h1.symm ((hF b hb).2.2.trans (h2.symm.trans (hF b' hb').2.2.symm))

/-- There are at most as many classes under symmetry as tilings. -/
theorem ncard_classes_le_ncard_similarTilings (n : ℕ) : (Classes n).ncard ≤ (SimilarTilings n).ncard :=
  Set.ncard_image_le (finite_similarTilingFinsets n)

/-- There are at most eight times as many tilings as classes under symmetry. -/
theorem ncard_similarTilings_le (n : ℕ) : (SimilarTilings n).ncard ≤ 8 * (Classes n).ncard := by
  classical
  have hfin := finite_similarTilingFinsets n
  have hC : Classes n = ↑(hfin.toFinset.image orbit) := by
    simp [Classes]
  rw [Set.ncard_eq_toFinset_card _ hfin, hC, Set.ncard_coe_finset]
  refine Finset.card_le_mul_card_image _ 8 fun C hC => ?_
  obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hC
  have hsub : (↑(hfin.toFinset.filter fun T' => orbit T' = orbit T) : Set (Finset Rect)) ⊆ orbit T := by
    intro T' hT'
    have := (Finset.mem_filter.mp (Finset.mem_coe.mp hT')).2
    rw [← this]
    exact mem_orbit_self T'
  rw [← Set.ncard_coe_finset]
  exact (Set.ncard_le_ncard hsub (ncard_orbit_le T).1).trans (ncard_orbit_le T).2

/-- **Proportions, bags, classes and tilings.** For the unit square and `n` tiles, with `a` the number of proportions, `c` the number of bags, `b` the number of classes under symmetry and `t` the number of tilings, `a ≤ c ≤ b ≤ t ≤ 8 b`. -/
theorem ncard_chain (n : ℕ) :
    (Proportions n).ncard ≤ (Bags n).ncard ∧ (Bags n).ncard ≤ (Classes n).ncard ∧
      (Classes n).ncard ≤ (SimilarTilings n).ncard ∧ (SimilarTilings n).ncard ≤ 8 * (Classes n).ncard :=
  ⟨ncard_proportions_le_ncard_bags n, ncard_bags_le_ncard_classes n,
    ncard_classes_le_ncard_similarTilings n, ncard_similarTilings_le n⟩

/-! ## The two notions of crossing -/

open Classical in
/-- **Crossings of lists and of sets.** A point is a corner of four tiles of a tiling exactly when it is the bottom-left corner of a tile, the bottom-right corner of another, the top-right corner of a third and the top-left corner of a fourth. -/
theorem IsTiling.isCrossing_iff_isSetCrossing {R : Rect} {tl : List Rect} (h : IsTiling R tl) {q : ℝ × ℝ} :
    IsCrossing tl q ↔ IsSetCrossing tl.toFinset q := by
  constructor
  · rintro ⟨l, hnd, hlen, hl⟩
    let kind : Rect → Bool × Bool := fun T => (decide (T.x = q.1), decide (T.y = q.2))
    have hinj : ∀ S ∈ l, ∀ T ∈ l, kind S = kind T → S = T := by
      intro S hS T hT hk
      simp only [kind, Prod.mk.injEq, decide_eq_decide] at hk
      obtain ⟨hSx, hSy⟩ := (hl S hS).2
      obtain ⟨hTx, hTy⟩ := (hl T hT).2
      refine h.eq_of_corner (hl S hS).1 (hl T hT).1 ?_ ?_
      · by_cases hc : S.x = q.1
        · exact Or.inl (hc.trans (hk.1.mp hc).symm)
        · exact Or.inr ((hSx.resolve_left hc).trans
            (hTx.resolve_left fun hT' => hc (hk.1.mpr hT')).symm)
      · by_cases hc : S.y = q.2
        · exact Or.inl (hc.trans (hk.2.mp hc).symm)
        · exact Or.inr ((hSy.resolve_left hc).trans
            (hTy.resolve_left fun hT' => hc (hk.2.mpr hT')).symm)
    have hmap : (l.map kind).Nodup := hnd.map_on hinj
    have hall : ∀ b : Bool × Bool, b ∈ l.map kind := by
      intro b
      have hcard : (l.map kind).toFinset.card = Fintype.card (Bool × Bool) := by
        rw [List.toFinset_card_of_nodup hmap, List.length_map, hlen]
        rfl
      have := Finset.eq_univ_of_card _ hcard
      exact List.mem_toFinset.mp (this ▸ Finset.mem_univ b)
    obtain ⟨A, hA, hkA⟩ := List.mem_map.mp (hall (true, true))
    obtain ⟨B, hB, hkB⟩ := List.mem_map.mp (hall (false, true))
    obtain ⟨C, hC, hkC⟩ := List.mem_map.mp (hall (false, false))
    obtain ⟨D, hD, hkD⟩ := List.mem_map.mp (hall (true, false))
    simp only [kind, Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not] at hkA hkB hkC hkD
    refine ⟨⟨A, List.mem_toFinset.mpr (hl A hA).1, Prod.ext hkA.1 hkA.2⟩,
      ⟨B, List.mem_toFinset.mpr (hl B hB).1, Prod.ext ((hl B hB).2.1.resolve_left hkB.1) hkB.2⟩,
      ⟨C, List.mem_toFinset.mpr (hl C hC).1,
        Prod.ext ((hl C hC).2.1.resolve_left hkC.1) ((hl C hC).2.2.resolve_left hkC.2)⟩,
      ⟨D, List.mem_toFinset.mpr (hl D hD).1, Prod.ext hkD.1 ((hl D hD).2.2.resolve_left hkD.2)⟩⟩
  · rintro ⟨⟨A, hA, eA⟩, ⟨B, hB, eB⟩, ⟨C, hC, eC⟩, ⟨D, hD, eD⟩⟩
    rw [List.mem_toFinset] at hA hB hC hD
    have a1 : A.x = q.1 := congrArg Prod.fst eA
    have a2 : A.y = q.2 := congrArg Prod.snd eA
    have b1 : B.x + B.w = q.1 := congrArg Prod.fst eB
    have b2 : B.y = q.2 := congrArg Prod.snd eB
    have c1 : C.x + C.w = q.1 := congrArg Prod.fst eC
    have c2 : C.y + C.h = q.2 := congrArg Prod.snd eC
    have d1 : D.x = q.1 := congrArg Prod.fst eD
    have d2 : D.y + D.h = q.2 := congrArg Prod.snd eD
    obtain ⟨hAw, hAh⟩ := h.nondegenerate A hA
    obtain ⟨hBw, hBh⟩ := h.nondegenerate B hB
    obtain ⟨hCw, hCh⟩ := h.nondegenerate C hC
    obtain ⟨hDw, hDh⟩ := h.nondegenerate D hD
    refine ⟨[A, B, C, D], ?_, rfl, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
        List.nodup_nil, and_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
      · rintro rfl
        linarith
    · intro T hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl
      · exact ⟨hA, Or.inl a1, Or.inl a2⟩
      · exact ⟨hB, Or.inr b1, Or.inl b2⟩
      · exact ⟨hC, Or.inr c1, Or.inr c2⟩
      · exact ⟨hD, Or.inl d1, Or.inr d2⟩

/-- **Crossings of a tiling given as a set.** A point is one at which four tiles of a tiling given as a set meet exactly when it is a corner of four tiles of a list of the tiles. -/
theorem IsSetTiling.isSetCrossing_iff {R : Rect} {T : Finset Rect} (h : IsSetTiling R T) {q : ℝ × ℝ} :
    IsSetCrossing T q ↔ IsCrossing T.toList q := by
  rw [h.toList.isCrossing_iff_isSetCrossing, Finset.toList_toFinset]

/-- **Tilings fixed by a quarter turn, with the crossing as a corner of four tiles.** A similar tiling of the unit square of proportion greater than one that is fixed by a quarter turn, in either direction, has the centre of the square as a corner of four tiles, and its number of tiles is a multiple of four. -/
theorem IsSimilarSetTiling.quarter_turn_isCrossing {x : ℝ} {T : Finset Rect} (hx : 1 < x)
    (h : IsSimilarSetTiling x (Rect.main 1 1) T) (hfix : T.image Rect.rot = T ∨ T.image Rect.rot^[3] = T) :
    IsCrossing T.toList (1 / 2, 1 / 2) ∧ 4 ∣ T.card :=
  ⟨h.toIsSetTiling.isSetCrossing_iff.mp (h.quarter_turn hx hfix).1, (h.quarter_turn hx hfix).2⟩

end Rectiling
