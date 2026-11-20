-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Refinement
import Rectiling.Scaling

/-!
# Persistence of proportions

A proportion with which a square can be cut into `n ≥ 2` similar rectangles serves for `n + k` rectangles as well, for every `k ≥ 3`.
Three tiles are gained by cutting a tile in four, five by cutting it in six, and four by surrounding a reduced copy of the tiling with a pinwheel of four tiles; squares are treated separately.
-/

namespace Rectiling

namespace Rect

/-- The four quarters of a rectangle. -/
noncomputable def four (r : Rect) : List Rect :=
  [⟨r.x, r.y, r.w / 2, r.h / 2⟩, ⟨r.x + r.w / 2, r.y, r.w / 2, r.h / 2⟩,
    ⟨r.x, r.y + r.h / 2, r.w / 2, r.h / 2⟩, ⟨r.x + r.w / 2, r.y + r.h / 2, r.w / 2, r.h / 2⟩]

/-- Six parts of a rectangle similar to it: one with two thirds of its sides and five with one third. -/
noncomputable def six (r : Rect) : List Rect :=
  [⟨r.x, r.y, r.w / 3 + r.w / 3, r.h / 3 + r.h / 3⟩,
    ⟨r.x, r.y + (r.h / 3 + r.h / 3), r.w / 3, r.h / 3⟩,
    ⟨r.x + r.w / 3, r.y + (r.h / 3 + r.h / 3), r.w / 3, r.h / 3⟩,
    ⟨r.x + (r.w / 3 + r.w / 3), r.y, r.w / 3, r.h / 3⟩,
    ⟨r.x + (r.w / 3 + r.w / 3), r.y + r.h / 3, r.w / 3, r.h / 3⟩,
    ⟨r.x + (r.w / 3 + r.w / 3), r.y + (r.h / 3 + r.h / 3), r.w / 3, r.h / 3⟩]

/-- Eight parts of a rectangle similar to it: one with three quarters of its sides and seven with one quarter. -/
noncomputable def eight (r : Rect) : List Rect :=
  [⟨r.x, r.y, r.w / 4 + r.w / 4 + r.w / 4, r.h / 4 + r.h / 4 + r.h / 4⟩,
    ⟨r.x, r.y + (r.h / 4 + r.h / 4 + r.h / 4), r.w / 4, r.h / 4⟩,
    ⟨r.x + r.w / 4, r.y + (r.h / 4 + r.h / 4 + r.h / 4), r.w / 4, r.h / 4⟩,
    ⟨r.x + (r.w / 4 + r.w / 4), r.y + (r.h / 4 + r.h / 4 + r.h / 4), r.w / 4, r.h / 4⟩,
    ⟨r.x + (r.w / 4 + r.w / 4 + r.w / 4), r.y, r.w / 4, r.h / 4⟩,
    ⟨r.x + (r.w / 4 + r.w / 4 + r.w / 4), r.y + r.h / 4, r.w / 4, r.h / 4⟩,
    ⟨r.x + (r.w / 4 + r.w / 4 + r.w / 4), r.y + (r.h / 4 + r.h / 4), r.w / 4, r.h / 4⟩,
    ⟨r.x + (r.w / 4 + r.w / 4 + r.w / 4), r.y + (r.h / 4 + r.h / 4 + r.h / 4), r.w / 4, r.h / 4⟩]

/-- The four outer tiles of the pinwheel in the unit square, with long side `p` and short side `q`. -/
def pinwheel (p q : ℝ) : List Rect :=
  [⟨0, 0, p, q⟩, ⟨p, 0, q, p⟩, ⟨q, p, p, q⟩, ⟨0, q, q, p⟩]

theorem isTiling_four {r : Rect} (hr : r.Nondegenerate) : IsTiling r r.four := by
  have hw : 0 < r.w / 2 := half_pos hr.1
  have hh : 0 < r.h / 2 := half_pos hr.2
  have h1 := IsTiling.hcat (x := r.x) (y := r.y) hw hw hh (isTiling_singleton ⟨hw, hh⟩)
    (isTiling_singleton ⟨hw, hh⟩)
  have h2 := IsTiling.hcat (x := r.x) (y := r.y + r.h / 2) hw hw hh (isTiling_singleton ⟨hw, hh⟩)
    (isTiling_singleton ⟨hw, hh⟩)
  have h3 := IsTiling.vcat (add_pos hw hw) hh hh h1 h2
  convert h3 using 1
  ext <;> simp
  rfl

theorem isTiling_six {r : Rect} (hr : r.Nondegenerate) : IsTiling r r.six := by
  have hw : 0 < r.w / 3 := div_pos hr.1 (by norm_num)
  have hh : 0 < r.h / 3 := div_pos hr.2 (by norm_num)
  have hw2 := add_pos hw hw
  have hh2 := add_pos hh hh
  have h1 := IsTiling.hcat (x := r.x) (y := r.y + (r.h / 3 + r.h / 3)) hw hw hh
    (isTiling_singleton ⟨hw, hh⟩) (isTiling_singleton ⟨hw, hh⟩)
  have h2 := IsTiling.vcat (x := r.x) (y := r.y) hw2 hh2 hh (isTiling_singleton ⟨hw2, hh2⟩) h1
  have h3 := IsTiling.vcat (x := r.x + (r.w / 3 + r.w / 3)) (y := r.y) hw hh hh
    (isTiling_singleton ⟨hw, hh⟩) (isTiling_singleton ⟨hw, hh⟩)
  have h4 := IsTiling.vcat (x := r.x + (r.w / 3 + r.w / 3)) (y := r.y) hw hh2 hh h3
    (isTiling_singleton ⟨hw, hh⟩)
  have h5 := IsTiling.hcat hw2 hw (add_pos hh2 hh) h2 h4
  convert h5 using 1
  ext
  · rfl
  · rfl
  · simp only
    ring
  · simp only
    ring
  · rfl

theorem isTiling_eight {r : Rect} (hr : r.Nondegenerate) : IsTiling r r.eight := by
  have hw : 0 < r.w / 4 := div_pos hr.1 (by norm_num)
  have hh : 0 < r.h / 4 := div_pos hr.2 (by norm_num)
  have hw2 := add_pos hw hw
  have hh2 := add_pos hh hh
  have hw3 := add_pos hw2 hw
  have hh3 := add_pos hh2 hh
  have h1 := IsTiling.hcat (x := r.x) (y := r.y + (r.h / 4 + r.h / 4 + r.h / 4)) hw hw hh
    (isTiling_singleton ⟨hw, hh⟩) (isTiling_singleton ⟨hw, hh⟩)
  have h2 := IsTiling.hcat (x := r.x) (y := r.y + (r.h / 4 + r.h / 4 + r.h / 4)) hw2 hw hh h1
    (isTiling_singleton ⟨hw, hh⟩)
  have h3 := IsTiling.vcat (x := r.x) (y := r.y) hw3 hh3 hh (isTiling_singleton ⟨hw3, hh3⟩) h2
  have h4 := IsTiling.vcat (x := r.x + (r.w / 4 + r.w / 4 + r.w / 4)) (y := r.y) hw hh hh
    (isTiling_singleton ⟨hw, hh⟩) (isTiling_singleton ⟨hw, hh⟩)
  have h5 := IsTiling.vcat (x := r.x + (r.w / 4 + r.w / 4 + r.w / 4)) (y := r.y) hw hh2 hh h4
    (isTiling_singleton ⟨hw, hh⟩)
  have h6 := IsTiling.vcat (x := r.x + (r.w / 4 + r.w / 4 + r.w / 4)) (y := r.y) hw hh3 hh h5
    (isTiling_singleton ⟨hw, hh⟩)
  have h7 := IsTiling.hcat hw3 hw (add_pos hh3 hh) h3 h6
  convert h7 using 1
  ext
  · rfl
  · rfl
  · simp only
    ring
  · simp only
    ring
  · rfl

theorem hasProportion_four {x : ℝ} {r : Rect} (h : r.HasProportion x) :
    ∀ t ∈ r.four, t.HasProportion x := by
  intro t ht
  simp only [four, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;>
    exact HasProportion.of_scaled (c := 1 / 2) (by dsimp only; ring) (by dsimp only; ring) h

theorem hasProportion_six {x : ℝ} {r : Rect} (h : r.HasProportion x) :
    ∀ t ∈ r.six, t.HasProportion x := by
  intro t ht
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact HasProportion.of_scaled (c := 2 / 3) (by dsimp only; ring) (by dsimp only; ring) h
  all_goals
    exact HasProportion.of_scaled (c := 1 / 3) (by dsimp only; ring) (by dsimp only; ring) h

theorem hasProportion_eight {x : ℝ} {r : Rect} (h : r.HasProportion x) :
    ∀ t ∈ r.eight, t.HasProportion x := by
  intro t ht
  simp only [eight, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact HasProportion.of_scaled (c := 3 / 4) (by dsimp only; ring) (by dsimp only; ring) h
  all_goals
    exact HasProportion.of_scaled (c := 1 / 4) (by dsimp only; ring) (by dsimp only; ring) h

/-- The pinwheel: four rectangles with sides `p > q`, where `p + q = 1`, and the square of side `p - q` that they surround tile the unit square. -/
theorem isTiling_pinwheel {p q : ℝ} (hq : 0 < q) (hqp : q < p) (hpq : p + q = 1) :
    IsTiling (main 1 1) (⟨q, q, p - q, p - q⟩ :: pinwheel p q) where
  nondegenerate t ht := by
    simp only [pinwheel, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> constructor <;> dsimp only <;> linarith
  cover := by
    ext ⟨a, b⟩
    simp only [pinwheel, main, Set.mem_iUnion, exists_prop, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp, exists_eq_left, mem_closed]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
        ⟨h1, h2, h3, h4⟩) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total b q with hbq | hbq
      · rcases le_total a p with hap | hap
        · right
          left
          refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
        · right
          right
          left
          refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
      · rcases le_total p b with hpb | hpb
        · rcases le_total q a with hqa | hqa
          · right
            right
            right
            left
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
          · right
            right
            right
            right
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
        · rcases le_total a q with haq | haq
          · right
            right
            right
            right
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
          · rcases le_total p a with hpa | hpa
            · right
              right
              left
              refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
            · left
              refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  disjoint := by
    simp only [pinwheel, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      apply disjoint_inner_of_separated <;> dsimp only
    · right; right; right; linarith
    · left; linarith
    · right; right; left; linarith
    · right; left; linarith
    · left; linarith
    · right; right; left; linarith
    · right; right; left; linarith
    · right; right; left; linarith
    · right; left; linarith
    · right; left; linarith

end Rect

/-- The rectangle `R` can be cut into `n` rectangles of proportion `x`. -/
def TilesWith (x : ℝ) (R : Rect) (n : ℕ) : Prop :=
  ∃ tiles : List Rect, tiles.length = n ∧ IsSimilarTiling x R tiles

/-- The unit square can be cut into `n` rectangles of proportion `x`. -/
def Achievable (n : ℕ) (x : ℝ) : Prop :=
  TilesWith x (Rect.main 1 1) n

/-- The transpose of a rectangle that can be cut into `n` rectangles of proportion `x` can be cut likewise. -/
theorem TilesWith.transpose {x : ℝ} {R : Rect} {n : ℕ} (h : TilesWith x R n) :
    TilesWith x R.transpose n := by
  obtain ⟨tiles, hlen, htil⟩ := h
  exact ⟨tiles.map Rect.transpose, by simp [hlen], htil.transpose⟩

/-- The image under a homothety of a rectangle that can be cut into `n` rectangles of proportion `x` can be cut likewise. -/
theorem TilesWith.scale {x c : ℝ} {R : Rect} {n : ℕ} (hc : 0 < c) (h : TilesWith x R n) :
    TilesWith x (R.scale c) n := by
  obtain ⟨tiles, hlen, htil⟩ := h
  exact ⟨tiles.map (Rect.scale c), by simp [hlen], htil.scale hc⟩

/-- **Inverse aspect ratio.** The main rectangles of aspect ratios `w` and `1 / w` can be cut into `n` rectangles of the same proportions. -/
theorem tilesWith_main_inv {x w : ℝ} {n : ℕ} (hw : 0 < w) :
    TilesWith x (Rect.main w 1) n ↔ TilesWith x (Rect.main (1 / w) 1) n := by
  have key : ∀ {v : ℝ}, 0 < v → TilesWith x (Rect.main v 1) n → TilesWith x (Rect.main (1 / v) 1) n := by
    intro v hv h
    have h' := h.transpose.scale (one_div_pos.mpr hv)
    have e : (Rect.main v 1).transpose.scale (1 / v) = Rect.main (1 / v) 1 := by
      simp [Rect.transpose, Rect.scale, Rect.main, hv.ne']
    rwa [e] at h'
  exact ⟨key hw, fun h => by simpa using key (one_div_pos.mpr hw) h⟩

/-- A tiling of a rectangle with positive sides has at least one tile. -/
theorem IsTiling.exists_cons {R : Rect} {tiles : List Rect} (hR : R.Nondegenerate)
    (h : IsTiling R tiles) : ∃ t rest, tiles = t :: rest := by
  have hp : (R.x, R.y) ∈ R.closed := by
    rw [Rect.mem_closed]
    exact ⟨le_refl _, by linarith [hR.1], le_refl _, by linarith [hR.2]⟩
  obtain ⟨t, ht, -⟩ := h.exists_mem hp
  cases tiles with
  | nil => simp at ht
  | cons a l => exact ⟨a, l, rfl⟩

/-- **Three more tiles.** A tile is cut into its four quarters. -/
theorem TilesWith.add_three {x : ℝ} {R : Rect} {n : ℕ} (hR : R.Nondegenerate)
    (h : TilesWith x R n) : TilesWith x R (n + 3) := by
  obtain ⟨tiles, hlen, htil⟩ := h
  obtain ⟨t, rest, rfl⟩ := htil.toIsTiling.exists_cons hR
  have ht := htil.nondegenerate t (List.mem_cons_self ..)
  have hp := htil.proportion t (List.mem_cons_self ..)
  refine ⟨t.four ++ rest, ?_, htil.refine (Rect.isTiling_four ht) (Rect.hasProportion_four hp)⟩
  rw [List.length_cons] at hlen
  simp only [List.length_append, Rect.four, List.length_cons, List.length_nil]
  omega

/-- **Five more tiles.** A tile is cut into six rectangles similar to it and with its orientation. -/
theorem TilesWith.add_five {x : ℝ} {R : Rect} {n : ℕ} (hR : R.Nondegenerate)
    (h : TilesWith x R n) : TilesWith x R (n + 5) := by
  obtain ⟨tiles, hlen, htil⟩ := h
  obtain ⟨t, rest, rfl⟩ := htil.toIsTiling.exists_cons hR
  have ht := htil.nondegenerate t (List.mem_cons_self ..)
  have hp := htil.proportion t (List.mem_cons_self ..)
  refine ⟨t.six ++ rest, ?_, htil.refine (Rect.isTiling_six ht) (Rect.hasProportion_six hp)⟩
  rw [List.length_cons] at hlen
  simp only [List.length_append, Rect.six, List.length_cons, List.length_nil]
  omega

theorem nondegenerate_main_one : (Rect.main 1 1).Nondegenerate :=
  ⟨one_pos, one_pos⟩

/-- **Seven more tiles.** A tile is cut into eight rectangles similar to it and with its orientation. -/
theorem TilesWith.add_seven {x : ℝ} {R : Rect} {n : ℕ} (hR : R.Nondegenerate)
    (h : TilesWith x R n) : TilesWith x R (n + 7) := by
  obtain ⟨tiles, hlen, htil⟩ := h
  obtain ⟨t, rest, rfl⟩ := htil.toIsTiling.exists_cons hR
  have ht := htil.nondegenerate t (List.mem_cons_self ..)
  have hp := htil.proportion t (List.mem_cons_self ..)
  refine ⟨t.eight ++ rest, ?_, htil.refine (Rect.isTiling_eight ht) (Rect.hasProportion_eight hp)⟩
  rw [List.length_cons] at hlen
  simp only [List.length_append, Rect.eight, List.length_cons, List.length_nil]
  omega

/-- **Five or more tiles.** A rectangle that can be cut into `n` rectangles of proportion `x` can be cut into `n + k`, for every `k ≥ 5`. -/
theorem TilesWith.add_of_five_le {x : ℝ} {R : Rect} {n : ℕ} (hR : R.Nondegenerate)
    (h : TilesWith x R n) : ∀ k : ℕ, 5 ≤ k → TilesWith x R (n + k)
  | 0, hk | 1, hk | 2, hk | 3, hk | 4, hk => by omega
  | 5, _ => h.add_five hR
  | 6, _ => (h.add_three hR).add_three hR
  | 7, _ => h.add_seven hR
  | k + 8, _ => (TilesWith.add_of_five_le hR h (k + 5) (by omega)).add_three hR

/-- **Four more tiles.** For a proportion greater than one, a pinwheel of four tiles surrounds a reduced copy of the tiling. -/
theorem Achievable.add_four {x : ℝ} {n : ℕ} (hx : 1 < x) (h : Achievable n x) :
    Achievable (n + 4) x := by
  obtain ⟨tiles, hlen, htil⟩ := h
  have hx0 : 0 < x + 1 := by linarith
  have hq : 0 < 1 / (x + 1) := div_pos one_pos hx0
  have hqp : 1 / (x + 1) < x / (x + 1) := div_lt_div_of_pos_right hx hx0
  have hpq : x / (x + 1) + 1 / (x + 1) = 1 := by
    field_simp
  have hpx : x / (x + 1) = x * (1 / (x + 1)) := by
    ring
  have hc : 0 < x / (x + 1) - 1 / (x + 1) := by linarith
  have hsub := (htil.scale hc).translate (1 / (x + 1)) (1 / (x + 1))
  have hrect : ((Rect.main 1 1).scale (x / (x + 1) - 1 / (x + 1))).translate (1 / (x + 1))
      (1 / (x + 1)) = ⟨1 / (x + 1), 1 / (x + 1), x / (x + 1) - 1 / (x + 1),
        x / (x + 1) - 1 / (x + 1)⟩ := by
    ext <;> simp [Rect.main, Rect.scale, Rect.translate]
  rw [hrect] at hsub
  refine ⟨_ ++ Rect.pinwheel (x / (x + 1)) (1 / (x + 1)), ?_,
    { toIsTiling := (Rect.isTiling_pinwheel hq hqp hpq).refine hsub.toIsTiling
      one_le := hx.le
      proportion := ?_ }⟩
  · simp only [List.length_append, List.length_map, Rect.pinwheel, List.length_cons,
      List.length_nil, hlen]
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsub.proportion t ht
    · simp only [Rect.pinwheel, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · left
        exact hpx
      · right
        exact hpx
      · left
        exact hpx
      · right
        exact hpx

/-- The unit square can be cut into `n` squares, for every `n ≥ 6`. -/
theorem achievable_one : ∀ n : ℕ, 6 ≤ n → Achievable n 1
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h => by omega
  | 6, _ => by
    have hp : (Rect.main 1 1).HasProportion 1 := by
      left
      simp [Rect.main]
    exact ⟨(Rect.main 1 1).six, rfl,
      { toIsTiling := Rect.isTiling_six nondegenerate_main_one
        one_le := le_refl _
        proportion := Rect.hasProportion_six hp }⟩
  | 7, _ => by
    have hp : (Rect.main 1 1).HasProportion 1 := by
      left
      simp [Rect.main]
    have h4 : Achievable 4 1 :=
      ⟨(Rect.main 1 1).four, rfl,
        { toIsTiling := Rect.isTiling_four nondegenerate_main_one
          one_le := le_refl _
          proportion := Rect.hasProportion_four hp }⟩
    exact h4.add_three nondegenerate_main_one
  | 8, _ => by
    have hp : (Rect.main 1 1).HasProportion 1 := by
      left
      simp [Rect.main]
    exact ⟨(Rect.main 1 1).eight, rfl,
      { toIsTiling := Rect.isTiling_eight nondegenerate_main_one
        one_le := le_refl _
        proportion := Rect.hasProportion_eight hp }⟩
  | n + 9, _ => (achievable_one (n + 6) (by omega)).add_three nondegenerate_main_one

/-- A proportion that serves for `n` tiles, other than the single square, serves for `n + 4` tiles. -/
theorem Achievable.add_four_of_two_le {x : ℝ} {n : ℕ} (hn : 2 ≤ n) (h : Achievable n x) :
    Achievable (n + 4) x := by
  obtain ⟨tiles, hlen, htil⟩ := h
  rcases htil.one_le.lt_or_eq with hx | hx
  · exact Achievable.add_four hx ⟨tiles, hlen, htil⟩
  · rw [← hx]
    exact achievable_one (n + 4) (by omega)

/-- **Persistence.** A proportion with which the unit square can be cut into `n ≥ 2` similar rectangles serves for `n + k` rectangles as well, for every `k ≥ 3`. -/
theorem persistence {x : ℝ} {n : ℕ} (hn : 2 ≤ n) (h : Achievable n x) :
    ∀ k : ℕ, 3 ≤ k → Achievable (n + k) x
  | 0, hk | 1, hk | 2, hk => by omega
  | 3, _ => h.add_three nondegenerate_main_one
  | 4, _ => h.add_four_of_two_le hn
  | 5, _ => h.add_five nondegenerate_main_one
  | k + 6, _ => (persistence hn h (k + 3) (by omega)).add_three nondegenerate_main_one

/-- **Persistence for proportions other than one.** For a proportion greater than one, the hypothesis on the number of tiles is not needed. -/
theorem persistence_of_one_lt {x : ℝ} {n : ℕ} (hx : 1 < x) (h : Achievable n x) :
    ∀ k : ℕ, 3 ≤ k → Achievable (n + k) x
  | 0, hk | 1, hk | 2, hk => by omega
  | 3, _ => h.add_three nondegenerate_main_one
  | 4, _ => h.add_four hx
  | 5, _ => h.add_five nondegenerate_main_one
  | k + 6, _ => (persistence_of_one_lt hx h (k + 3) (by omega)).add_three nondegenerate_main_one

end Rectiling
