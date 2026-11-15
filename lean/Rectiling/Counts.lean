-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Persistence

/-!
# Tilings, classes and bags

Tilings as finite sets of rectangles, the symmetries of the unit square acting on them, and the sets counted by the numbers of tilings, of classes under symmetry, of bags and of proportions.
The parity of the number of tilings, the tilings fixed by the reflection in a diagonal or by a quarter turn, and the existence, for every number of tiles from six onwards, of two bags with the same proportion.
The finiteness of the sets counted is not proved here: the statements on cardinalities take it as a hypothesis.
-/

namespace Rectiling

noncomputable instance : DecidableEq Rect :=
  Classical.decEq _

/-! ## Tilings as sets of rectangles -/

/-- Tiling of a rectangle by a finite set of rectangles. -/
structure IsSetTiling (R : Rect) (T : Finset Rect) : Prop where
  /-- Every tile has positive sides. -/
  nondegenerate : ∀ t ∈ T, t.Nondegenerate
  /-- The union of the closed tiles is the closed rectangle. -/
  cover : (⋃ t ∈ T, t.closed) = R.closed
  /-- Distinct open tiles are disjoint. -/
  disjoint : (T : Set Rect).Pairwise fun s t => Disjoint s.inner t.inner

/-- Tiling of a rectangle by a finite set of rectangles of proportion `x`, with `x` not smaller than one. -/
structure IsSimilarSetTiling (x : ℝ) (R : Rect) (T : Finset Rect) : Prop extends IsSetTiling R T where
  /-- The proportion is not smaller than one. -/
  one_le : 1 ≤ x
  /-- Every tile has the given proportion. -/
  proportion : ∀ t ∈ T, t.HasProportion x

/-- The tiles of a tiling given as a list are distinct. -/
theorem IsTiling.nodup {R : Rect} {l : List Rect} (h : IsTiling R l) : l.Nodup := by
  refine h.disjoint.imp_of_mem ?_
  intro a b ha _ hab heq
  rw [← heq] at hab
  exact Rect.not_disjoint_inner_self (h.nondegenerate a ha) hab

/-- The set of the tiles of a tiling given as a list is a tiling. -/
theorem IsTiling.toSet {R : Rect} {l : List Rect} (h : IsTiling R l) : IsSetTiling R l.toFinset where
  nondegenerate t ht := h.nondegenerate t (List.mem_toFinset.mp ht)
  cover := by
    rw [← h.cover]
    ext p
    simp
  disjoint := by
    intro s hs t ht hne
    by_contra hd
    exact hne (h.eq_of_not_disjoint (List.mem_toFinset.mp hs) (List.mem_toFinset.mp ht) hd)

/-- A list without repetitions whose set of elements is a tiling is a tiling. -/
theorem IsSetTiling.of_nodup {R : Rect} {l : List Rect} (hl : l.Nodup) (h : IsSetTiling R l.toFinset) :
    IsTiling R l where
  nondegenerate t ht := h.nondegenerate t (List.mem_toFinset.mpr ht)
  cover := by
    rw [← h.cover]
    ext p
    simp
  disjoint := by
    refine hl.pairwise_of_forall_ne ?_
    intro a ha b hb hne
    exact h.disjoint (by simpa using ha) (by simpa using hb) hne

/-- **Lists and sets.** A list is a tiling exactly when it has no repetitions and its set of elements is a tiling. -/
theorem isTiling_iff_isSetTiling {R : Rect} {l : List Rect} :
    IsTiling R l ↔ l.Nodup ∧ IsSetTiling R l.toFinset :=
  ⟨fun h => ⟨h.nodup, h.toSet⟩, fun h => IsSetTiling.of_nodup h.1 h.2⟩

/-- Two tilings given as lists have the same set of tiles exactly when one is a rearrangement of the other. -/
theorem IsTiling.toFinset_eq_iff_perm {R R' : Rect} {l l' : List Rect} (h : IsTiling R l)
    (h' : IsTiling R' l') : l.toFinset = l'.toFinset ↔ l.Perm l' :=
  ⟨fun e => List.perm_of_nodup_nodup_toFinset_eq h.nodup h'.nodup e, fun p => List.toFinset_eq_of_perm _ _ p⟩

/-- A list of the tiles of a tiling given as a set is a tiling. -/
theorem IsSetTiling.toList {R : Rect} {T : Finset Rect} (h : IsSetTiling R T) : IsTiling R T.toList :=
  IsSetTiling.of_nodup T.nodup_toList (by rwa [Finset.toList_toFinset])

theorem IsSimilarTiling.toSet {x : ℝ} {R : Rect} {l : List Rect} (h : IsSimilarTiling x R l) :
    IsSimilarSetTiling x R l.toFinset where
  toIsSetTiling := h.toIsTiling.toSet
  one_le := h.one_le
  proportion t ht := h.proportion t (List.mem_toFinset.mp ht)

theorem IsSimilarSetTiling.toList {x : ℝ} {R : Rect} {T : Finset Rect} (h : IsSimilarSetTiling x R T) :
    IsSimilarTiling x R T.toList where
  toIsTiling := h.toIsSetTiling.toList
  one_le := h.one_le
  proportion t ht := h.proportion t (Finset.mem_toList.mp ht)

/-- **Lists and sets, for similar tilings.** A finite set is a similar tiling exactly when it is the set of the tiles of a similar tiling given as a list, and the list then has as many terms as the set has elements. -/
theorem isSimilarSetTiling_iff {x : ℝ} {R : Rect} {T : Finset Rect} {n : ℕ} :
    T.card = n ∧ IsSimilarSetTiling x R T ↔
      ∃ l : List Rect, l.toFinset = T ∧ l.length = n ∧ IsSimilarTiling x R l := by
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨T.toList, Finset.toList_toFinset T, by rw [Finset.length_toList, hn], h.toList⟩
  · rintro ⟨l, rfl, hn, h⟩
    exact ⟨by rw [List.toFinset_card_of_nodup h.toIsTiling.nodup, hn], h.toSet⟩

theorem IsSimilarTiling.perm {x : ℝ} {R : Rect} {l l' : List Rect} (h : IsSimilarTiling x R l)
    (hp : l.Perm l') : IsSimilarTiling x R l' where
  toIsTiling := h.toIsTiling.perm hp
  one_le := h.one_le
  proportion t ht := h.proportion t (hp.mem_iff.mpr ht)

namespace IsSetTiling

variable {R : Rect} {T : Finset Rect}

theorem subset (h : IsSetTiling R T) {t : Rect} (ht : t ∈ T) : t.closed ⊆ R.closed :=
  h.toList.subset (Finset.mem_toList.mpr ht)

theorem exists_mem (h : IsSetTiling R T) {p : ℝ × ℝ} (hp : p ∈ R.closed) : ∃ t ∈ T, p ∈ t.closed := by
  obtain ⟨t, ht, hpt⟩ := h.toList.exists_mem hp
  exact ⟨t, Finset.mem_toList.mp ht, hpt⟩

/-- Two tiles of a tiling whose interiors meet are equal. -/
theorem eq_of_not_disjoint (h : IsSetTiling R T) {s t : Rect} (hs : s ∈ T) (ht : t ∈ T)
    (hst : ¬Disjoint s.inner t.inner) : s = t :=
  h.toList.eq_of_not_disjoint (Finset.mem_toList.mpr hs) (Finset.mem_toList.mpr ht) hst

end IsSetTiling

namespace Rect

/-- A square with positive sides has no proportion other than one. -/
theorem HasProportion.eq_one {x : ℝ} {t : Rect} (hp : t.HasProportion x) (ht : t.Nondegenerate)
    (hwh : t.w = t.h) : x = 1 := by
  have key : (x - 1) * t.h = 0 := by
    rcases hp with hp | hp
    · linarith
    · rw [hwh] at hp
      linarith
  rcases mul_eq_zero.mp key with h | h
  · linarith
  · linarith [ht.2]

/-- A rectangle with positive sides has at most one proportion not smaller than one. -/
theorem HasProportion.unique {x x' : ℝ} {t : Rect} (hp : t.HasProportion x) (hp' : t.HasProportion x')
    (ht : t.Nondegenerate) (hx : 1 ≤ x) (hx' : 1 ≤ x') : x = x' := by
  have cross : ∀ {y y' : ℝ}, 1 ≤ y → 1 ≤ y' → t.w = y * t.h → t.h = y' * t.w → y = y' := by
    intro y y' hy hy' h1 h2
    have h3 : t.w * 1 = t.w * (y * y') := by
      rw [h2] at h1
      linarith
    have h4 : y * y' = 1 := (mul_left_cancel₀ ht.1.ne' h3).symm
    have h5 : y ≤ y * y' := le_mul_of_one_le_right (by linarith) hy'
    have h6 : y' ≤ y * y' := le_mul_of_one_le_left (by linarith) hy
    linarith
  rcases hp with hp | hp <;> rcases hp' with hp' | hp'
  · exact mul_right_cancel₀ ht.2.ne' (hp.symm.trans hp')
  · exact cross hx hx' hp hp'
  · exact (cross hx' hx hp' hp).symm
  · exact mul_right_cancel₀ ht.1.ne' (hp.symm.trans hp')

end Rect

/-- The proportion of a similar tiling of a rectangle with positive sides is determined by its tiles. -/
theorem IsSimilarSetTiling.proportion_unique {x x' : ℝ} {R : Rect} {T : Finset Rect}
    (hR : R.Nondegenerate) (h : IsSimilarSetTiling x R T) (h' : IsSimilarSetTiling x' R T) : x = x' := by
  have hp : (R.x, R.y) ∈ R.closed := by
    rw [Rect.mem_closed]
    exact ⟨le_refl _, by linarith [hR.1], le_refl _, by linarith [hR.2]⟩
  obtain ⟨t, ht, -⟩ := h.exists_mem hp
  exact (h.proportion t ht).unique (h'.proportion t ht) (h.nondegenerate t ht) h.one_le h'.one_le

/-! ## The symmetries of the unit square -/

namespace Rect

/-- The image under the quarter turn about the centre of the unit square, which sends `(u, v)` to `(1 - v, u)`. -/
def rot (r : Rect) : Rect :=
  ⟨1 - r.y - r.h, r.x, r.h, r.w⟩

/-- The image under the reflection of the unit square in its second diagonal, which sends `(u, v)` to `(1 - v, 1 - u)`. -/
def antitranspose (r : Rect) : Rect :=
  ⟨1 - r.y - r.h, 1 - r.x - r.w, r.h, r.w⟩

/-- The image under one of the eight symmetries of the unit square: an optional transposition followed by a number of quarter turns. -/
def sym (e : Bool) (k : ℕ) (r : Rect) : Rect :=
  rot^[k] (bif e then r.transpose else r)

theorem mem_closed_rot {r : Rect} {p : ℝ × ℝ} : p ∈ r.rot.closed ↔ (p.2, 1 - p.1) ∈ r.closed := by
  simp only [mem_closed, rot]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_inner_rot {r : Rect} {p : ℝ × ℝ} : p ∈ r.rot.inner ↔ (p.2, 1 - p.1) ∈ r.inner := by
  simp only [mem_inner, rot]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem hasProportion_rot {x : ℝ} {r : Rect} : r.rot.HasProportion x ↔ r.HasProportion x := by
  simp [HasProportion, rot, or_comm]

theorem nondegenerate_rot {r : Rect} : r.rot.Nondegenerate ↔ r.Nondegenerate := by
  simp [Nondegenerate, rot, and_comm]

/-- Four quarter turns are the identity. -/
@[simp]
theorem rot_rot_rot_rot (r : Rect) : r.rot.rot.rot.rot = r := by
  ext <;> simp only [rot] <;> ring

theorem rot_injective : Function.Injective rot :=
  fun a b hab => by
    have := congrArg (fun r : Rect => r.rot.rot.rot) hab
    simpa using this

theorem transpose_injective : Function.Injective transpose :=
  Function.LeftInverse.injective (g := transpose) transpose_transpose

/-- The reflection in the second diagonal is the transposition followed by a half turn. -/
theorem antitranspose_eq (r : Rect) : r.antitranspose = sym true 2 r := by
  ext <;> simp [antitranspose, sym, rot, transpose]

theorem iterate_four_mul_rot (k : ℕ) (r : Rect) : rot^[4 * k] r = r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply]
    simpa using ih

/-- A quarter turn followed by the transposition is the transposition followed by three quarter turns. -/
theorem transpose_rot (r : Rect) : r.rot.transpose = r.transpose.rot.rot.rot := by
  ext <;> simp only [rot, transpose]
  ring

theorem transpose_iterate_rot (k : ℕ) (r : Rect) : (rot^[k] r).transpose = rot^[3 * k] r.transpose := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, transpose_rot, Nat.mul_succ, Function.iterate_add_apply]
    rfl

/-- The composite of two symmetries is a symmetry. -/
theorem sym_sym (e e' : Bool) (k k' : ℕ) (r : Rect) :
    sym e k (sym e' k' r) = sym (xor e e') (k + (bif e then 3 * k' else k')) r := by
  cases e <;> cases e' <;>
    simp [sym, transpose_iterate_rot, Function.iterate_add_apply]

/-- Every symmetry has an inverse among the symmetries. -/
theorem sym_inverse (e : Bool) (k : ℕ) (r : Rect) : sym e (bif e then k else 3 * k) (sym e k r) = r := by
  rw [sym_sym]
  cases e
  · have h : 3 * k + k = 4 * k := by ring
    simp [sym, h, iterate_four_mul_rot]
  · have h : k + 3 * k = 4 * k := by ring
    simp [sym, h, iterate_four_mul_rot]

theorem sym_injective (e : Bool) (k : ℕ) : Function.Injective (sym e k) :=
  Function.LeftInverse.injective (g := sym e (bif e then k else 3 * k)) (sym_inverse e k)

end Rect

/-- The images of the tiles of a tiling of the unit square under the quarter turn tile the unit square. -/
theorem IsTiling.rot {l : List Rect} (h : IsTiling (Rect.main 1 1) l) :
    IsTiling (Rect.main 1 1) (l.map Rect.rot) where
  nondegenerate t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact Rect.nondegenerate_rot.mpr (h.nondegenerate s hs)
  cover := by
    ext p
    have hcov := h.cover
    rw [Set.ext_iff] at hcov
    have hp := hcov (p.2, 1 - p.1)
    simp only [Set.mem_iUnion, exists_prop] at hp
    simp only [Set.mem_iUnion, exists_prop, List.mem_map, exists_exists_and_eq_and,
      Rect.mem_closed_rot]
    rw [hp, Rect.mem_closed, Rect.mem_closed]
    simp only [Rect.main]
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  disjoint := by
    rw [List.pairwise_map]
    refine h.disjoint.imp ?_
    intro a b hab
    rw [Set.disjoint_left] at hab ⊢
    intro p hpa hpb
    exact hab (Rect.mem_inner_rot.mp hpa) (Rect.mem_inner_rot.mp hpb)

theorem IsSimilarTiling.rot {x : ℝ} {l : List Rect} (h : IsSimilarTiling x (Rect.main 1 1) l) :
    IsSimilarTiling x (Rect.main 1 1) (l.map Rect.rot) where
  toIsTiling := h.toIsTiling.rot
  one_le := h.one_le
  proportion t ht := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact Rect.hasProportion_rot.mpr (h.proportion s hs)

theorem toFinset_map (f : Rect → Rect) (l : List Rect) : (l.map f).toFinset = l.toFinset.image f := by
  ext t
  simp

namespace IsSimilarSetTiling

variable {x : ℝ} {T : Finset Rect}

/-- The transposes of the tiles of a similar tiling of the unit square form a similar tiling of the unit square, of the same proportion. -/
theorem transpose (h : IsSimilarSetTiling x (Rect.main 1 1) T) :
    IsSimilarSetTiling x (Rect.main 1 1) (T.image Rect.transpose) := by
  have h' := h.toList.transpose.toSet
  rwa [toFinset_map, Finset.toList_toFinset] at h'

/-- The images of the tiles of a similar tiling of the unit square under the quarter turn form a similar tiling of the unit square, of the same proportion. -/
theorem rot (h : IsSimilarSetTiling x (Rect.main 1 1) T) :
    IsSimilarSetTiling x (Rect.main 1 1) (T.image Rect.rot) := by
  have h' := h.toList.rot.toSet
  rwa [toFinset_map, Finset.toList_toFinset] at h'

theorem iterate_rot (h : IsSimilarSetTiling x (Rect.main 1 1) T) (k : ℕ) :
    IsSimilarSetTiling x (Rect.main 1 1) (T.image Rect.rot^[k]) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have h' := ih.rot
    rwa [Finset.image_image, ← Function.iterate_succ'] at h'

/-- The images of the tiles of a similar tiling of the unit square under a symmetry of the square form a similar tiling of the unit square, of the same proportion. -/
theorem sym (h : IsSimilarSetTiling x (Rect.main 1 1) T) (e : Bool) (k : ℕ) :
    IsSimilarSetTiling x (Rect.main 1 1) (T.image (Rect.sym e k)) := by
  cases e
  · exact h.iterate_rot k
  · have h' := h.transpose.iterate_rot k
    rwa [Finset.image_image] at h'

end IsSimilarSetTiling

/-! ## The sets counted -/

/-- The similar tilings of the unit square with `n` tiles, as sets of rectangles; `t(n)` is the cardinality of this set. -/
def SimilarTilings (n : ℕ) : Set (Finset Rect) :=
  {T | T.card = n ∧ ∃ x, IsSimilarSetTiling x (Rect.main 1 1) T}

/-- The tilings of the unit square by `n` squares, as sets of rectangles. -/
def SquareTilings (n : ℕ) : Set (Finset Rect) :=
  {T | T.card = n ∧ IsSimilarSetTiling 1 (Rect.main 1 1) T}

/-- The similar tilings of the unit square with `n` tiles of proportion greater than one, as sets of rectangles. -/
def OblongTilings (n : ℕ) : Set (Finset Rect) :=
  {T | T.card = n ∧ ∃ x, 1 < x ∧ IsSimilarSetTiling x (Rect.main 1 1) T}

/-- The orbit of a set of rectangles under the eight symmetries of the unit square. -/
def orbit (T : Finset Rect) : Set (Finset Rect) :=
  {T' | ∃ e k, T' = T.image (Rect.sym e k)}

/-- The orbits of the similar tilings of the unit square with `n` tiles under the symmetries of the square; `b(n)` is the cardinality of this set. -/
def Classes (n : ℕ) : Set (Set (Finset Rect)) :=
  orbit '' SimilarTilings n

/-- The short side of a rectangle. -/
noncomputable def Rect.short (r : Rect) : ℝ :=
  min r.w r.h

/-- The bags of the similar tilings of the unit square with `n` tiles: pairs of the proportion and the multiset of the short sides of the tiles; `c(n)` is the cardinality of this set. -/
def Bags (n : ℕ) : Set (ℝ × Multiset ℝ) :=
  {b | ∃ x T, T.card = n ∧ IsSimilarSetTiling x (Rect.main 1 1) T ∧ b = (x, T.val.map Rect.short)}

/-- The proportions of the similar tilings of the unit square with `n` tiles; `a(n)` is the cardinality of this set. -/
def Proportions (n : ℕ) : Set ℝ :=
  {x | ∃ T : Finset Rect, T.card = n ∧ IsSimilarSetTiling x (Rect.main 1 1) T}

/-- The similar tilings with `n` tiles, as sets, are the sets of tiles of the similar tilings given as lists of `n` rectangles. -/
theorem mem_similarTilings_iff {n : ℕ} {T : Finset Rect} :
    T ∈ SimilarTilings n ↔
      ∃ (l : List Rect) (x : ℝ), l.toFinset = T ∧ l.length = n ∧ IsSimilarTiling x (Rect.main 1 1) l := by
  constructor
  · rintro ⟨hn, x, h⟩
    obtain ⟨l, h1, h2, h3⟩ := isSimilarSetTiling_iff.mp ⟨hn, h⟩
    exact ⟨l, x, h1, h2, h3⟩
  · rintro ⟨l, x, h1, h2, h3⟩
    have h := isSimilarSetTiling_iff.mpr ⟨l, h1, h2, h3⟩
    exact ⟨h.1, x, h.2⟩

/-- The proportions counted are those with which the unit square can be cut into `n` similar rectangles. -/
theorem mem_proportions_iff {n : ℕ} {x : ℝ} : x ∈ Proportions n ↔ Achievable n x := by
  constructor
  · rintro ⟨T, hn, h⟩
    obtain ⟨l, -, h2, h3⟩ := isSimilarSetTiling_iff.mp ⟨hn, h⟩
    exact ⟨l, h2, h3⟩
  · rintro ⟨l, h2, h3⟩
    have h := isSimilarSetTiling_iff.mpr ⟨l, rfl, h2, h3⟩
    exact ⟨_, h.1, h.2⟩

/-- The bag of a similar tiling given as a list. -/
theorem mem_bags_of_list {x : ℝ} {l : List Rect} (h : IsSimilarTiling x (Rect.main 1 1) l) :
    (x, ((l.map Rect.short : List ℝ) : Multiset ℝ)) ∈ Bags l.length := by
  refine ⟨x, l.toFinset, List.toFinset_card_of_nodup h.toIsTiling.nodup, h.toSet, ?_⟩
  rw [List.toFinset_val, h.toIsTiling.nodup.dedup, Multiset.map_coe]

/-- The proportion of a bag is a surjection from the bags onto the proportions. -/
theorem image_fst_bags (n : ℕ) : Prod.fst '' Bags n = Proportions n := by
  ext x
  constructor
  · rintro ⟨b, ⟨y, T, hn, h, rfl⟩, rfl⟩
    exact ⟨T, hn, h⟩
  · rintro ⟨T, hn, h⟩
    exact ⟨_, ⟨x, T, hn, h, rfl⟩, rfl⟩

/-- A symmetry of the square maps the similar tilings of the unit square with `n` tiles to themselves. -/
theorem image_sym_mem_similarTilings {n : ℕ} {T : Finset Rect} (h : T ∈ SimilarTilings n) (e : Bool)
    (k : ℕ) : T.image (Rect.sym e k) ∈ SimilarTilings n := by
  obtain ⟨hn, x, hx⟩ := h
  exact ⟨by rw [Finset.card_image_of_injective _ (Rect.sym_injective e k), hn], x, hx.sym e k⟩

theorem mem_orbit_self (T : Finset Rect) : T ∈ orbit T :=
  ⟨false, 0, by
    have : Rect.sym false 0 = id := rfl
    rw [this, Finset.image_id]⟩

/-- The orbit of a similar tiling of the unit square with `n` tiles consists of such tilings. -/
theorem orbit_subset_similarTilings {n : ℕ} {T : Finset Rect} (h : T ∈ SimilarTilings n) :
    orbit T ⊆ SimilarTilings n := by
  rintro T' ⟨e, k, rfl⟩
  exact image_sym_mem_similarTilings h e k

/-- The orbits are the classes of an equivalence relation. -/
theorem orbit_eq_of_mem {T T' : Finset Rect} (h : T' ∈ orbit T) : orbit T' = orbit T := by
  obtain ⟨e, k, rfl⟩ := h
  ext T''
  constructor
  · rintro ⟨e', k', rfl⟩
    refine ⟨xor e' e, k' + (bif e' then 3 * k else k), ?_⟩
    rw [Finset.image_image]
    congr 1
    funext r
    exact Rect.sym_sym e' e k' k r
  · rintro ⟨e', k', rfl⟩
    refine ⟨xor e' e, k' + (bif e' then 3 * (bif e then k else 3 * k) else (bif e then k else 3 * k)), ?_⟩
    rw [Finset.image_image]
    congr 1
    funext r
    simp only [Function.comp_apply]
    rw [← Rect.sym_sym, Rect.sym_inverse]

/-- A similar tiling of the unit square is a tiling by squares or has proportion greater than one. -/
theorem similarTilings_eq_union (n : ℕ) : SimilarTilings n = SquareTilings n ∪ OblongTilings n := by
  ext T
  constructor
  · rintro ⟨hn, x, hx⟩
    rcases hx.one_le.eq_or_lt with h | h
    · left
      subst h
      exact ⟨hn, hx⟩
    · right
      exact ⟨hn, x, h, hx⟩
  · rintro (⟨hn, h⟩ | ⟨hn, x, -, h⟩)
    · exact ⟨hn, 1, h⟩
    · exact ⟨hn, x, h⟩

theorem disjoint_squareTilings_oblongTilings (n : ℕ) : Disjoint (SquareTilings n) (OblongTilings n) := by
  rw [Set.disjoint_left]
  rintro T ⟨-, h1⟩ ⟨-, x, hx, h⟩
  have := h1.proportion_unique nondegenerate_main_one h
  linarith

/-! ## Tilings fixed by a reflection in a diagonal -/

/-- A tile of a tiling of the unit square that contains a corner of the square, and whose image under a map that exchanges width and height is a tile with the same corner, is a square. -/
theorem IsSetTiling.square_of_corner {T : Finset Rect} (h : IsSetTiling (Rect.main 1 1) T) {t u : Rect}
    (ht : t ∈ T) (hu : u ∈ T) (hw : u.w = t.h)
    (hx : max t.x u.x < min (t.x + t.w) (u.x + u.w)) (hy : max t.y u.y < min (t.y + t.h) (u.y + u.h)) :
    t.w = t.h := by
  have := h.eq_of_not_disjoint ht hu (Rect.not_disjoint_inner_of_overlap hx hy)
  rw [← hw, this]

/-- **Reflection in the first diagonal.** A similar tiling of the unit square that is mapped into itself by the transposition has proportion one. -/
theorem IsSimilarSetTiling.eq_one_of_transpose {x : ℝ} {T : Finset Rect}
    (h : IsSimilarSetTiling x (Rect.main 1 1) T) (hfix : ∀ t ∈ T, t.transpose ∈ T) : x = 1 := by
  have hp : ((0 : ℝ), (0 : ℝ)) ∈ (Rect.main 1 1).closed := by
    simp [Rect.mem_closed, Rect.main]
  obtain ⟨t, ht, hpt⟩ := h.exists_mem hp
  have hnd := h.nondegenerate t ht
  have hc : (t.x, t.y) ∈ (Rect.main 1 1).closed := by
    apply h.subset ht
    rw [Rect.mem_closed]
    exact ⟨le_refl _, by linarith [hnd.1], le_refl _, by linarith [hnd.2]⟩
  rw [Rect.mem_closed] at hpt hc
  simp only [Rect.main] at hpt hc
  have hx0 : t.x = 0 := le_antisymm hpt.1 hc.1
  have hy0 : t.y = 0 := le_antisymm hpt.2.2.1 hc.2.2.1
  refine (h.proportion t ht).eq_one hnd (h.square_of_corner ht (hfix t ht) rfl ?_ ?_)
  · simp only [Rect.transpose, hx0, hy0, max_self, zero_add, lt_min_iff]
    exact ⟨hnd.1, hnd.2⟩
  · simp only [Rect.transpose, hx0, hy0, max_self, zero_add, lt_min_iff]
    exact ⟨hnd.2, hnd.1⟩

/-- **Reflection in the second diagonal.** A similar tiling of the unit square that is mapped into itself by the reflection in the second diagonal has proportion one. -/
theorem IsSimilarSetTiling.eq_one_of_antitranspose {x : ℝ} {T : Finset Rect}
    (h : IsSimilarSetTiling x (Rect.main 1 1) T) (hfix : ∀ t ∈ T, t.antitranspose ∈ T) : x = 1 := by
  have hp : ((1 : ℝ), (0 : ℝ)) ∈ (Rect.main 1 1).closed := by
    simp [Rect.mem_closed, Rect.main]
  obtain ⟨t, ht, hpt⟩ := h.exists_mem hp
  have hnd := h.nondegenerate t ht
  have hc : (t.x + t.w, t.y) ∈ (Rect.main 1 1).closed := by
    apply h.subset ht
    rw [Rect.mem_closed]
    exact ⟨by linarith [hnd.1], le_refl _, le_refl _, by linarith [hnd.2]⟩
  rw [Rect.mem_closed] at hpt hc
  simp only [Rect.main] at hpt hc
  have hx1 : t.x + t.w = 1 := le_antisymm (by linarith [hc.2.1]) hpt.2.1
  have hy0 : t.y = 0 := le_antisymm hpt.2.2.1 hc.2.2.1
  refine (h.proportion t ht).eq_one hnd (h.square_of_corner ht (hfix t ht) rfl ?_ ?_)
  · simp only [Rect.antitranspose, max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hnd.1, hnd.2]
  · simp only [Rect.antitranspose, max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hnd.1, hnd.2]

/-- The tiles of a similar tiling of proportion one are squares. -/
theorem IsSimilarSetTiling.square {R : Rect} {T : Finset Rect} (h : IsSimilarSetTiling 1 R T) {t : Rect}
    (ht : t ∈ T) : t.w = t.h := by
  rcases h.proportion t ht with hp | hp <;> linarith

/-- **Tilings fixed by the reflection in a diagonal.** A similar tiling of the unit square that is fixed by the reflection in either diagonal consists of squares. -/
theorem IsSimilarSetTiling.squares_of_reflection {x : ℝ} {T : Finset Rect}
    (h : IsSimilarSetTiling x (Rect.main 1 1) T)
    (hfix : T.image Rect.transpose = T ∨ T.image Rect.antitranspose = T) :
    x = 1 ∧ ∀ t ∈ T, t.w = t.h := by
  have hx : x = 1 := by
    rcases hfix with hfix | hfix
    · refine h.eq_one_of_transpose fun t ht => ?_
      rw [← hfix]
      exact Finset.mem_image_of_mem _ ht
    · refine h.eq_one_of_antitranspose fun t ht => ?_
      rw [← hfix]
      exact Finset.mem_image_of_mem _ ht
  subst hx
  exact ⟨rfl, fun t ht => h.square ht⟩

/-! ## The parity of the number of tilings -/

/-- The transposition is an involution on sets of rectangles. -/
theorem image_transpose_image_transpose (T : Finset Rect) :
    (T.image Rect.transpose).image Rect.transpose = T := by
  rw [Finset.image_image]
  have : Rect.transpose ∘ Rect.transpose = id := by
    funext r
    rfl
  rw [this, Finset.image_id]

/-- The transposition maps the similar tilings of the unit square with `n` tiles of proportion greater than one to themselves. -/
theorem image_transpose_mem_oblongTilings {n : ℕ} {T : Finset Rect} (h : T ∈ OblongTilings n) :
    T.image Rect.transpose ∈ OblongTilings n := by
  obtain ⟨hn, x, hx, hT⟩ := h
  exact ⟨by rw [Finset.card_image_of_injective _ Rect.transpose_injective, hn], x, hx, hT.transpose⟩

/-- **No fixed point.** The transposition fixes no similar tiling of the unit square of proportion greater than one. -/
theorem image_transpose_ne {n : ℕ} {T : Finset Rect} (h : T ∈ OblongTilings n) :
    T.image Rect.transpose ≠ T := by
  obtain ⟨-, x, hx, hT⟩ := h
  intro hfix
  have := (hT.squares_of_reflection (Or.inl hfix)).1
  linarith

/-- A finite set with an involution without fixed points has an even number of elements. -/
theorem even_ncard_of_involution {α : Type*} {s : Set α} (hs : s.Finite) (f : α → α)
    (hmem : ∀ a ∈ s, f a ∈ s) (hinv : ∀ a ∈ s, f (f a) = a) (hne : ∀ a ∈ s, f a ≠ a) :
    Even s.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs]
  have hsum : ∑ _a ∈ hs.toFinset, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun a _ => f a) ?_ ?_ ?_ ?_
    · intro a _
      decide
    · intro a ha _
      exact hne a (hs.mem_toFinset.mp ha)
    · intro a ha
      exact hs.mem_toFinset.mpr (hmem a (hs.mem_toFinset.mp ha))
    · intro a ha
      exact hinv a (hs.mem_toFinset.mp ha)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact (ZMod.natCast_eq_zero_iff_even).mp hsum

/-- The number of similar tilings of the unit square with `n` tiles of proportion greater than one is even, if finite. -/
theorem even_ncard_oblongTilings (n : ℕ) (hfin : (OblongTilings n).Finite) :
    Even (OblongTilings n).ncard :=
  even_ncard_of_involution hfin (fun T => T.image Rect.transpose)
    (fun _ h => image_transpose_mem_oblongTilings h) (fun T _ => image_transpose_image_transpose T)
    (fun _ h => image_transpose_ne h)

/-- **Parity of the number of tilings.** The number of similar tilings of the unit square with `n` tiles has the parity of the number of tilings of the unit square by `n` squares. The finiteness of the set of tilings is a hypothesis, to be discharged separately. -/
theorem ncard_similarTilings_mod_two (n : ℕ) (hfin : (SimilarTilings n).Finite) :
    (SimilarTilings n).ncard % 2 = (SquareTilings n).ncard % 2 := by
  rw [similarTilings_eq_union] at hfin ⊢
  have h1 := hfin.subset Set.subset_union_left
  have h2 := hfin.subset Set.subset_union_right
  rw [Set.ncard_union_eq (disjoint_squareTilings_oblongTilings n) h1 h2]
  obtain ⟨m, hm⟩ := even_ncard_oblongTilings n h2
  omega

/-! ## Tilings fixed by a quarter turn -/

/-- A point at which four rectangles of a set meet: it is the bottom-left corner of one, the bottom-right corner of another, the top-right corner of a third and the top-left corner of a fourth. -/
def IsCrossing (T : Finset Rect) (p : ℝ × ℝ) : Prop :=
  (∃ t ∈ T, (t.x, t.y) = p) ∧ (∃ t ∈ T, (t.x + t.w, t.y) = p) ∧
    (∃ t ∈ T, (t.x + t.w, t.y + t.h) = p) ∧ ∃ t ∈ T, (t.x, t.y + t.h) = p

namespace Rect

/-- A rectangle that contains the centre of the unit square other than as a corner overlaps its image under the quarter turn. -/
theorem not_disjoint_rot {t : Rect} (ht : t.Nondegenerate) (hc : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ t.closed)
    (h : ¬((t.x = 1 / 2 ∨ t.x + t.w = 1 / 2) ∧ (t.y = 1 / 2 ∨ t.y + t.h = 1 / 2))) :
    ¬Disjoint t.inner t.rot.inner := by
  rw [mem_closed] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only at h1 h2 h3 h4
  have hw := ht.1
  have hh := ht.2
  have hcases : (t.x < 1 / 2 ∧ 1 / 2 < t.x + t.w) ∨ (t.y < 1 / 2 ∧ 1 / 2 < t.y + t.h) := by
    by_contra hcon
    rw [not_or] at hcon
    apply h
    constructor
    · by_contra hx
      rw [not_or] at hx
      exact hcon.1 ⟨lt_of_le_of_ne h1 hx.1, lt_of_le_of_ne h2 (Ne.symm hx.2)⟩
    · by_contra hy
      rw [not_or] at hy
      exact hcon.2 ⟨lt_of_le_of_ne h3 hy.1, lt_of_le_of_ne h4 (Ne.symm hy.2)⟩
  apply not_disjoint_inner_of_overlap
  · simp only [rot, max_lt_iff, lt_min_iff]
    rcases hcases with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · simp only [rot, max_lt_iff, lt_min_iff]
    rcases hcases with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The four images of a rectangle under the quarter turns. -/
noncomputable def turns (t : Rect) : Finset Rect :=
  {t, t.rot, t.rot.rot, t.rot.rot.rot}

theorem mem_turns_self (t : Rect) : t ∈ t.turns := by
  simp [turns]

theorem turns_rot (t : Rect) : t.rot.turns = t.turns := by
  ext u
  simp only [turns, rot_rot_rot_rot, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem turns_eq_of_mem {t u : Rect} (h : u ∈ t.turns) : u.turns = t.turns := by
  simp only [turns, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · rw [turns_rot]
  · rw [turns_rot, turns_rot]
  · rw [turns_rot, turns_rot, turns_rot]

/-- A rectangle that is not a square and is not fixed by the half turn has four distinct images under the quarter turns. -/
theorem card_turns {t : Rect} (hwh : t.w ≠ t.h) (h2 : t.rot.rot ≠ t) : t.turns.card = 4 := by
  have h01 : t ≠ t.rot := fun e => hwh (congrArg Rect.w e)
  have h03 : t ≠ t.rot.rot.rot := fun e => hwh (congrArg Rect.w e)
  have h12 : t.rot ≠ t.rot.rot := fun e => hwh (congrArg Rect.w e).symm
  have h23 : t.rot.rot ≠ t.rot.rot.rot := fun e => hwh (congrArg Rect.w e)
  have h13 : t.rot ≠ t.rot.rot.rot := fun e => h2 (rot_injective e).symm
  rw [turns, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h23]
  · simp [h12, h13]
  · simp [h01, h2.symm, h03]

end Rect

namespace IsSimilarSetTiling

variable {x : ℝ} {T : Finset Rect}

/-- In a similar tiling of the unit square of proportion greater than one that is mapped into itself by the quarter turn, the centre of the square is a corner of every tile that contains it. -/
theorem corner_of_rot (hx : 1 < x) (h : IsSimilarSetTiling x (Rect.main 1 1) T)
    (hfix : ∀ t ∈ T, t.rot ∈ T) {t : Rect} (ht : t ∈ T) (hc : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ t.closed) :
    (t.x = 1 / 2 ∨ t.x + t.w = 1 / 2) ∧ (t.y = 1 / 2 ∨ t.y + t.h = 1 / 2) := by
  by_contra hcon
  have hnd := h.nondegenerate t ht
  have he := h.eq_of_not_disjoint ht (hfix t ht) (Rect.not_disjoint_rot hnd hc hcon)
  have hwh : t.w = t.h := (congrArg Rect.w he).trans rfl
  have := (h.proportion t ht).eq_one hnd hwh
  linarith

theorem ne_of_one_lt (hx : 1 < x) {R : Rect} (h : IsSimilarSetTiling x R T) {t : Rect} (ht : t ∈ T) :
    t.w ≠ t.h := by
  intro hwh
  have := (h.proportion t ht).eq_one (h.nondegenerate t ht) hwh
  linarith

/-- In a similar tiling of the unit square of proportion greater than one that is mapped into itself by the quarter turn, no tile is fixed by the half turn. -/
theorem rot_rot_ne (hx : 1 < x) (h : IsSimilarSetTiling x (Rect.main 1 1) T)
    (hfix : ∀ t ∈ T, t.rot ∈ T) {t : Rect} (ht : t ∈ T) : t.rot.rot ≠ t := by
  intro he
  have hnd := h.nondegenerate t ht
  have h1 : 1 - t.x - t.w = t.x := congrArg Rect.x he
  have h2 : 1 - t.y - t.h = t.y := congrArg Rect.y he
  have hc : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ t.closed := by
    rw [Rect.mem_closed]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith [hnd.1, hnd.2]
  rcases (h.corner_of_rot hx hfix ht hc).1 with h3 | h3 <;> linarith [hnd.1]

/-- **Crossing at the centre.** In a similar tiling of the unit square of proportion greater than one that is mapped into itself by the quarter turn, four tiles meet at the centre of the square. -/
theorem isCrossing_of_rot (hx : 1 < x) (h : IsSimilarSetTiling x (Rect.main 1 1) T)
    (hfix : ∀ t ∈ T, t.rot ∈ T) : IsCrossing T (1 / 2, 1 / 2) := by
  have hp : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ (Rect.main 1 1).closed := by
    rw [Rect.mem_closed]
    simp only [Rect.main]
    norm_num
  obtain ⟨t, m0, hc⟩ := h.exists_mem hp
  have m1 := hfix _ m0
  have m2 := hfix _ m1
  have m3 := hfix _ m2
  have hcor := h.corner_of_rot hx hfix m0 hc
  rcases hcor with ⟨h1 | h1, h2 | h2⟩
  · refine ⟨⟨_, m0, ?_⟩, ⟨_, m1, ?_⟩, ⟨_, m2, ?_⟩, ⟨_, m3, ?_⟩⟩ <;>
      refine Prod.ext ?_ ?_ <;> simp only [Rect.rot] <;> linarith
  · refine ⟨⟨_, m1, ?_⟩, ⟨_, m2, ?_⟩, ⟨_, m3, ?_⟩, ⟨_, m0, ?_⟩⟩ <;>
      refine Prod.ext ?_ ?_ <;> simp only [Rect.rot] <;> linarith
  · refine ⟨⟨_, m3, ?_⟩, ⟨_, m0, ?_⟩, ⟨_, m1, ?_⟩, ⟨_, m2, ?_⟩⟩ <;>
      refine Prod.ext ?_ ?_ <;> simp only [Rect.rot] <;> linarith
  · refine ⟨⟨_, m2, ?_⟩, ⟨_, m3, ?_⟩, ⟨_, m0, ?_⟩, ⟨_, m1, ?_⟩⟩ <;>
      refine Prod.ext ?_ ?_ <;> simp only [Rect.rot] <;> linarith

/-- **Orbits of four.** A similar tiling of the unit square of proportion greater than one that is mapped into itself by the quarter turn has a number of tiles divisible by four. -/
theorem four_dvd_card_of_rot (hx : 1 < x) (h : IsSimilarSetTiling x (Rect.main 1 1) T)
    (hfix : ∀ t ∈ T, t.rot ∈ T) : 4 ∣ T.card := by
  have hsub : ∀ u ∈ T, ∀ t ∈ u.turns, t ∈ T := by
    intro u hu t ht
    simp only [Rect.turns, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hu
    · exact hfix _ hu
    · exact hfix _ (hfix _ hu)
    · exact hfix _ (hfix _ (hfix _ hu))
  have hfib : ∀ O ∈ T.image Rect.turns, (T.filter fun t => t.turns = O).card = 4 := by
    intro O hO
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hO
    have : (T.filter fun t => t.turns = u.turns) = u.turns := by
      ext t
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨-, he⟩
        rw [← he]
        exact t.mem_turns_self
      · intro ht
        exact ⟨hsub u hu t ht, Rect.turns_eq_of_mem ht⟩
    rw [this]
    exact Rect.card_turns (h.ne_of_one_lt hx hu) (h.rot_rot_ne hx hfix hu)
  have hcard := Finset.card_eq_sum_card_fiberwise (f := Rect.turns) (s := T) (t := T.image Rect.turns)
    (fun t ht => Finset.mem_image_of_mem _ ht)
  rw [hcard, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  exact Dvd.intro_left _ rfl

/-- **Tilings fixed by a quarter turn.** A similar tiling of the unit square of proportion greater than one that is fixed by a quarter turn, in either direction, has four tiles meeting at the centre of the square, and its number of tiles is a multiple of four. -/
theorem quarter_turn (hx : 1 < x) (h : IsSimilarSetTiling x (Rect.main 1 1) T)
    (hfix : T.image Rect.rot = T ∨ T.image Rect.rot^[3] = T) :
    IsCrossing T (1 / 2, 1 / 2) ∧ 4 ∣ T.card := by
  have hfix' : ∀ t ∈ T, t.rot ∈ T := by
    rcases hfix with hfix | hfix
    · intro t ht
      rw [← hfix]
      exact Finset.mem_image_of_mem _ ht
    · have h3 : ∀ t ∈ T, t.rot.rot.rot ∈ T := by
        intro t ht
        rw [← hfix]
        exact Finset.mem_image_of_mem Rect.rot^[3] ht
      intro t ht
      have := h3 _ (h3 _ (h3 _ ht))
      simpa using this
  exact ⟨h.isCrossing_of_rot hx hfix', h.four_dvd_card_of_rot hx hfix'⟩

end IsSimilarSetTiling

/-! ## Bags -/

namespace Rect

/-- The short sides of the four quarters of a rectangle add up to twice its short side. -/
theorem sum_short_four (t : Rect) : (t.four.map short).sum = 2 * t.short := by
  have h : min (t.w / 2) (t.h / 2) = min t.w t.h / 2 := min_div_div_right (by norm_num) t.w t.h
  simp only [four, short, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h]
  ring

/-- A row of congruent rectangles of width `a` and height `h`, starting at the point `(x, y)`. -/
def row (x y a h : ℝ) : ℕ → List Rect
  | 0 => []
  | k + 1 => row x y a h k ++ [⟨x + k * a, y, a, h⟩]

theorem length_row (x y a h : ℝ) (k : ℕ) : (row x y a h k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [row, ih]

theorem mem_row {x y a h : ℝ} {k : ℕ} {t : Rect} (ht : t ∈ row x y a h k) : t.w = a ∧ t.h = h := by
  induction k with
  | zero => simp [row] at ht
  | succ k ih =>
    simp only [row, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih ht
    · exact ⟨rfl, rfl⟩

/-- A row of `k + 1` congruent rectangles tiles the rectangle that they span. -/
theorem isTiling_row {x y a h : ℝ} (ha : 0 < a) (hh : 0 < h) (k : ℕ) :
    IsTiling ⟨x, y, (k + 1) * a, h⟩ (row x y a h (k + 1)) := by
  induction k with
  | zero =>
    have := isTiling_singleton (r := ⟨x, y, a, h⟩) ⟨ha, hh⟩
    simpa [row] using this
  | succ k ih =>
    have hk : (0 : ℝ) < (k + 1) * a := by positivity
    have := IsTiling.hcat hk ha hh ih (isTiling_singleton (r := ⟨x + (k + 1) * a, y, a, h⟩) ⟨ha, hh⟩)
    have e : ((k + 1 : ℕ) + 1 : ℝ) * a = (k + 1) * a + a := by
      push_cast
      ring
    rw [e]
    rw [row]
    push_cast
    exact this

end Rect

/-- **Two sizes.** For every `k ≥ 1`, the unit square has a similar tiling with `k + 2` tiles in which two tiles have different short sides: a wide tile above a row of `k + 1` congruent wide tiles. -/
theorem exists_two_sizes (k : ℕ) (hk : 1 ≤ k) :
    ∃ (x : ℝ) (l : List Rect) (t u : Rect), l.length = k + 2 ∧ IsSimilarTiling x (Rect.main 1 1) l ∧
      t ∈ l ∧ u ∈ l ∧ t.short ≠ u.short := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (0 : ℝ) < k + 1 := by linarith
  have h2 : (0 : ℝ) < k + 2 := by linarith
  have ha : (0 : ℝ) < 1 / (k + 1) := one_div_pos.mpr h1
  have hb : (0 : ℝ) < 1 / (k + 2) := one_div_pos.mpr h2
  have hc : (0 : ℝ) < (k + 1) / (k + 2) := div_pos h1 h2
  have hrow := Rect.isTiling_row (x := 0) (y := 0) ha hb k
  have e1 : ((k : ℝ) + 1) * (1 / (k + 1)) = 1 := by
    field_simp
  have e2 : 1 / ((k : ℝ) + 2) + (k + 1) / (k + 2) = 1 := by
    field_simp
    ring
  rw [e1] at hrow
  have htil := IsTiling.vcat one_pos hb hc hrow
    (isTiling_singleton (r := ⟨0, 0 + 1 / (k + 2), 1, (k + 1) / (k + 2)⟩) ⟨one_pos, hc⟩)
  rw [e2] at htil
  refine ⟨(k + 2) / (k + 1), _, ⟨0, 0 + 1 / (k + 2), 1, (k + 1) / (k + 2)⟩,
    ⟨0 + k * (1 / (k + 1)), 0, 1 / (k + 1), 1 / (k + 2)⟩, ?_, ⟨htil, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [Rect.length_row]
  · rw [le_div_iff₀ h1]
    linarith
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨hw, hh⟩ := Rect.mem_row ht
      left
      rw [hw, hh]
      field_simp
    · rw [List.mem_singleton] at ht
      subst ht
      left
      simp only
      field_simp
  · simp
  · simp [Rect.row]
  · have hle1 : ((k : ℝ) + 1) / (k + 2) ≤ 1 := by
      rw [div_le_one h2]
      linarith
    have hle2 : 1 / ((k : ℝ) + 2) ≤ 1 / (k + 1) := one_div_le_one_div_of_le h1 (by linarith)
    simp only [Rect.short]
    rw [min_eq_right hle1, min_eq_right hle2]
    intro he
    rw [div_left_inj' h2.ne'] at he
    linarith

/-- **Two bags from two sizes.** If two tiles of a similar tiling have different short sides, cutting one or the other into its four quarters gives two similar tilings with three more tiles, of the same proportion, whose multisets of short sides differ. -/
theorem exists_bags_ne {x : ℝ} {R : Rect} {l : List Rect} (h : IsSimilarTiling x R l) {t u : Rect}
    (ht : t ∈ l) (hu : u ∈ l) (hne : t.short ≠ u.short) :
    ∃ l₁ l₂ : List Rect, l₁.length = l.length + 3 ∧ l₂.length = l.length + 3 ∧
      IsSimilarTiling x R l₁ ∧ IsSimilarTiling x R l₂ ∧
      ((l₁.map Rect.short : List ℝ) : Multiset ℝ) ≠ ((l₂.map Rect.short : List ℝ) : Multiset ℝ) := by
  have htu : u ≠ t := by
    rintro rfl
    exact hne rfl
  have hu' : u ∈ l.erase t := (List.mem_erase_of_ne htu).mpr hu
  have p : l.Perm (t :: u :: (l.erase t).erase u) :=
    (List.perm_cons_erase ht).trans ((List.perm_cons_erase hu').cons t)
  have hlen : l.length = ((l.erase t).erase u).length + 2 := by
    rw [p.length_eq]
    rfl
  have h1 := h.perm p
  have h2 := h1.perm (List.Perm.swap u t _)
  refine ⟨t.four ++ u :: (l.erase t).erase u, u.four ++ t :: (l.erase t).erase u, ?_, ?_,
    h1.refine (Rect.isTiling_four (h.nondegenerate t ht)) (Rect.hasProportion_four (h.proportion t ht)),
    h2.refine (Rect.isTiling_four (h.nondegenerate u hu)) (Rect.hasProportion_four (h.proportion u hu)),
    ?_⟩
  · rw [hlen]
    simp [Rect.four]
  · rw [hlen]
    simp [Rect.four]
  · intro he
    have hs := congrArg Multiset.sum he
    rw [Multiset.sum_coe, Multiset.sum_coe, List.map_append, List.map_append, List.sum_append,
      List.sum_append, Rect.sum_short_four, Rect.sum_short_four, List.map_cons, List.map_cons,
      List.sum_cons, List.sum_cons] at hs
    apply hne
    linarith

/-- **Two bags with the same proportion.** For every `n ≥ 6` there are two similar tilings of the unit square with `n` tiles that have the same proportion and different bags. -/
theorem exists_two_bags (n : ℕ) (hn : 6 ≤ n) :
    ∃ (x : ℝ) (m₁ m₂ : Multiset ℝ), (x, m₁) ∈ Bags n ∧ (x, m₂) ∈ Bags n ∧ m₁ ≠ m₂ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 2 + 3 := ⟨n - 6, by omega⟩
  obtain ⟨x, l, t, u, hlen, htil, ht, hu, hne⟩ := exists_two_sizes (k + 1) (by omega)
  obtain ⟨l₁, l₂, hl₁, hl₂, h₁, h₂, hb⟩ := exists_bags_ne htil ht hu hne
  refine ⟨x, _, _, ?_, ?_, hb⟩
  · have := mem_bags_of_list h₁
    rwa [hl₁, hlen] at this
  · have := mem_bags_of_list h₂
    rwa [hl₂, hlen] at this

/-- The map from bags to proportions is not injective for `n ≥ 6`. -/
theorem not_injOn_fst_bags (n : ℕ) (hn : 6 ≤ n) : ¬Set.InjOn Prod.fst (Bags n) := by
  obtain ⟨x, m₁, m₂, h₁, h₂, hne⟩ := exists_two_bags n hn
  intro hinj
  have := hinj h₁ h₂ rfl
  exact hne (Prod.ext_iff.mp this).2

/-- **More bags than proportions.** For every `n ≥ 6`, the number of bags of the similar tilings of the unit square with `n` tiles is greater than the number of their proportions. The finiteness of the set of bags is a hypothesis, to be discharged separately. -/
theorem ncard_proportions_lt_ncard_bags (n : ℕ) (hn : 6 ≤ n) (hfin : (Bags n).Finite) :
    (Proportions n).ncard < (Bags n).ncard := by
  obtain ⟨x, m₁, m₂, h₁, h₂, hne⟩ := exists_two_bags n hn
  have hsub : Proportions n ⊆ Prod.fst '' (Bags n \ {(x, m₁)}) := by
    rw [← image_fst_bags]
    rintro y ⟨b, hb, rfl⟩
    by_cases hbe : b = (x, m₁)
    · refine ⟨(x, m₂), ⟨h₂, ?_⟩, by rw [hbe]⟩
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and]
      exact hne.symm
    · exact ⟨b, ⟨hb, hbe⟩, rfl⟩
  have hfin' : (Bags n \ {(x, m₁)}).Finite := hfin.subset Set.sdiff_subset
  calc (Proportions n).ncard ≤ (Prod.fst '' (Bags n \ {(x, m₁)})).ncard :=
        Set.ncard_le_ncard hsub (hfin'.image _)
    _ ≤ (Bags n \ {(x, m₁)}).ncard := Set.ncard_image_le hfin'
    _ < (Bags n).ncard := Set.ncard_sdiff_singleton_lt_of_mem h₁ hfin

end Rectiling
