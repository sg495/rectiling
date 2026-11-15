-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.ProportionBound

/-!
# Finiteness of the set of similar tilings

The unit square has finitely many similar tilings with a given number of tiles.
For a given proportion, a tiling is determined by the networks of the heights of the tiling and of its transpose, with their orientation vectors and with the vertices numbered: the flow of value one on the first gives the width, the height and the ordinate of every tile, and the flow on the second gives its abscissa.
-/

namespace Rectiling

namespace Network

variable {V E V' E' : Type*} [Fintype V] [Fintype E] [DecidableEq V] [Fintype V'] [Fintype E'] [DecidableEq V']

omit [Fintype V] [Fintype V'] in
theorem Iso.div_eq {R : Type*} [CommRing R] {N : Network V E} {N' : Network V' E'} (I : Iso N N') (i : E → R)
    (v : V) : N'.div (fun e' => i (I.toE.symm e')) (I.toV v) = N.div i v := by
  simp only [div]
  rw [← Equiv.sum_comp I.toE]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [I.tail, I.head]

omit [Fintype V] [Fintype V'] in
/-- A flow is carried to a flow by an isomorphism of networks. -/
theorem Iso.isFlow {N : Network V E} {N' : Network V' E'} (I : Iso N N') {r : E → ℝ} {J : ℝ} {φ : V → ℝ}
    {i : E → ℝ} (h : N.IsFlow r J φ i) :
    N'.IsFlow (fun e' => r (I.toE.symm e')) J (fun v' => φ (I.toV.symm v')) (fun e' => i (I.toE.symm e')) where
  ohm e' := by
    obtain ⟨e, rfl⟩ := I.toE.surjective e'
    simp only [I.tail, I.head, Equiv.symm_apply_apply]
    exact h.ohm e
  kirchhoff v' := by
    obtain ⟨v, rfl⟩ := I.toV.surjective v'
    rw [I.div_eq, h.kirchhoff, I.source, I.sink]
    simp

end Network

variable {n : ℕ} {x : ℝ} {tl tl' : List Rect}

/-- The network of the heights of a list of `n` tiles, with its vertices and its edges numbered from zero. -/
noncomputable def heightNet (tl : List Rect) (hlen : tl.length = n) :
    Network (Fin (Fintype.card {c : ℝ // c ∈ levels tl})) (Fin n) where
  tail e := Fintype.equivFin _ ((heightNetwork 1 tl).tail ((finCongr hlen).symm e))
  head e := Fintype.equivFin _ ((heightNetwork 1 tl).head ((finCongr hlen).symm e))
  source := Fintype.equivFin _ (heightNetwork 1 tl).source
  sink := Fintype.equivFin _ (heightNetwork 1 tl).sink

/-- The numbering of the vertices and of the edges is an isomorphism. -/
noncomputable def heightNetIso (tl : List Rect) (hlen : tl.length = n) :
    Network.Iso (heightNetwork 1 tl) (heightNet tl hlen) where
  toV := Fintype.equivFin _
  toE := finCongr hlen
  tail e := by simp [heightNet]
  head e := by simp [heightNet]
  source := rfl
  sink := rfl

/-- The numbered network of the heights of a tiling of the unit square with its orientation vector for the proportion `x`. -/
noncomputable def heightPair (x : ℝ) (tl : List Rect) (hlen : tl.length = n) (h : IsTiling (Rect.main 1 1) tl) :
    Pair n where
  order := ⟨Fintype.card {c : ℝ // c ∈ levels tl}, by
    rw [Fintype.card_coe, ← hlen]
    exact Nat.lt_succ_of_le (card_levels_le tl)⟩
  net := heightNet tl hlen
  proper := (heightNetIso tl hlen).proper (h.heightNetwork_proper one_pos one_pos)
  tall e := tallVector x tl ((finCongr hlen).symm e)

/-- The tiles of a similar tiling of the unit square are given by any flow of value one, with potential zero at the sink, of a network isomorphic to the network of its heights. -/
theorem IsSimilarTiling.eq_of_isFlow (h : IsSimilarTiling x (Rect.main 1 1) tl) {k : ℕ}
    {N' : Network (Fin k) (Fin n)} {ε : Fin n → Bool} (I : Network.Iso (heightNetwork 1 tl) N')
    (hε : ∀ e, ε (I.toE e) = tallVector x tl e) {φ₀ : Fin k → ℝ} {i₀ : Fin n → ℝ}
    (hf : N'.IsFlow (fun e => if ε e then x else x⁻¹) 1 φ₀ i₀) (h0 : φ₀ N'.sink = 0) (e : Fin tl.length) :
    (tl.get e).w = i₀ (I.toE e) ∧ (tl.get e).y = φ₀ (N'.head (I.toE e)) ∧
      (tl.get e).h = (if ε (I.toE e) then x else x⁻¹) * i₀ (I.toE e) := by
  have hx : 0 < x := lt_of_lt_of_le one_pos h.one_le
  have hN := h.toIsTiling.heightNetwork_proper one_pos one_pos
  have hF := I.isFlow (h.toIsTiling.heightNetwork_isFlow one_pos one_pos)
  have hr : (fun e' => (tl.get (I.toE.symm e')).h / (tl.get (I.toE.symm e')).w) =
      fun e' => if ε e' then x else x⁻¹ := by
    funext e'
    rw [h.resistance_eq, ← hε, Equiv.apply_symm_apply]
  have hF' : N'.IsFlow (fun e' => if ε e' then x else x⁻¹) 1 (fun v' => (I.toV.symm v').1)
      (fun e' => (tl.get (I.toE.symm e')).w) := by
    rw [← hr]
    exact hF
  obtain ⟨hi, hφ⟩ := hF'.unique (I.proper hN) (fun e => by
    split_ifs
    · exact hx
    · exact inv_pos.mpr hx) hf
  have hs : (I.toV.symm N'.sink).1 = 0 := by
    rw [I.sink, Equiv.symm_apply_apply]
    rfl
  have hφ' : ∀ v, (I.toV.symm v).1 = φ₀ v := fun v => by
    have := hφ v
    rw [hs, h0] at this
    linarith
  have hw : (tl.get e).w = i₀ (I.toE e) := by
    have := congrFun hi (I.toE e)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  refine ⟨hw, ?_, ?_⟩
  · rw [← hφ', I.head, Equiv.symm_apply_apply, h.toIsTiling.head_val one_pos one_pos]
  · rw [← hw, hε, ← h.resistance_eq, div_mul_cancel₀ _ (h.toIsTiling.get_bounds e).1.ne']

/-- Two similar tilings of the unit square of the same proportion whose numbered networks of heights and orientation vectors coincide have tiles of the same widths and heights at the same ordinates. -/
theorem IsSimilarTiling.get_eq_of_heightPair_eq (h : IsSimilarTiling x (Rect.main 1 1) tl)
    (h' : IsSimilarTiling x (Rect.main 1 1) tl') (hlen : tl.length = n) (hlen' : tl'.length = n)
    (hp : heightPair x tl hlen h.toIsTiling = heightPair x tl' hlen' h'.toIsTiling) (j : Fin n) :
    (tl.get ((finCongr hlen).symm j)).y = (tl'.get ((finCongr hlen').symm j)).y ∧
      (tl.get ((finCongr hlen).symm j)).w = (tl'.get ((finCongr hlen').symm j)).w ∧
      (tl.get ((finCongr hlen).symm j)).h = (tl'.get ((finCongr hlen').symm j)).h := by
  have hx : 0 < x := lt_of_lt_of_le one_pos h.one_le
  have key : ∀ p : Pair n, p = heightPair x tl' hlen' h'.toIsTiling →
      ∃ I' : Network.Iso (heightNetwork 1 tl') p.net,
        (∀ e, I'.toE e = finCongr hlen' e) ∧ ∀ e, p.tall (I'.toE e) = tallVector x tl' e := by
    rintro _ rfl
    exact ⟨heightNetIso tl' hlen', fun _ => rfl, fun e => by simp [heightPair, heightNetIso]⟩
  obtain ⟨I', hE', hε'⟩ := key _ hp
  obtain ⟨I, hE, hε⟩ : ∃ I : Network.Iso (heightNetwork 1 tl) (heightPair x tl hlen h.toIsTiling).net,
      (∀ e, I.toE e = finCongr hlen e) ∧
        ∀ e, (heightPair x tl hlen h.toIsTiling).tall (I.toE e) = tallVector x tl e :=
    ⟨heightNetIso tl hlen, fun _ => rfl, fun e => by simp [heightPair, heightNetIso]⟩
  obtain ⟨φ₀, i₀, hf⟩ := (heightPair x tl hlen h.toIsTiling).proper.exists_isFlow
    (r := fun e => if (heightPair x tl hlen h.toIsTiling).tall e then x else x⁻¹) (fun e => by
      split_ifs
      · exact hx
      · exact inv_pos.mpr hx) 1
  have hf0 : (heightPair x tl hlen h.toIsTiling).net.IsFlow
      (fun e => if (heightPair x tl hlen h.toIsTiling).tall e then x else x⁻¹) 1
      (fun v => φ₀ v - φ₀ (heightPair x tl hlen h.toIsTiling).net.sink) i₀ :=
    ⟨fun e => by
      have := hf.ohm e
      simp only [sub_sub_sub_cancel_right]
      exact this, hf.kirchhoff⟩
  have A := h.eq_of_isFlow I hε hf0 (sub_self _) ((finCongr hlen).symm j)
  have B := h'.eq_of_isFlow I' hε' hf0 (sub_self _) ((finCongr hlen').symm j)
  rw [hE, Equiv.apply_symm_apply] at A
  rw [hE', Equiv.apply_symm_apply] at B
  exact ⟨A.2.1.trans B.2.1.symm, A.1.trans B.1.symm, A.2.2.trans B.2.2.symm⟩

/-- Two similar tilings of the unit square of the same proportion are equal when the numbered networks of heights and the orientation vectors of the tilings coincide and those of their transposes coincide. -/
theorem IsSimilarTiling.eq_of_heightPair_eq (h : IsSimilarTiling x (Rect.main 1 1) tl)
    (h' : IsSimilarTiling x (Rect.main 1 1) tl') (hlen : tl.length = n) (hlen' : tl'.length = n)
    (hT : IsSimilarTiling x (Rect.main 1 1) (tl.map Rect.transpose))
    (hT' : IsSimilarTiling x (Rect.main 1 1) (tl'.map Rect.transpose))
    (hlenT : (tl.map Rect.transpose).length = n) (hlenT' : (tl'.map Rect.transpose).length = n)
    (hp : heightPair x tl hlen h.toIsTiling = heightPair x tl' hlen' h'.toIsTiling)
    (hpT : heightPair x (tl.map Rect.transpose) hlenT hT.toIsTiling =
      heightPair x (tl'.map Rect.transpose) hlenT' hT'.toIsTiling) : tl = tl' := by
  refine List.ext_get (hlen.trans hlen'.symm) fun i h1 h2 => ?_
  have A := h.get_eq_of_heightPair_eq h' hlen hlen' hp ⟨i, hlen ▸ h1⟩
  have B := hT.get_eq_of_heightPair_eq hT' hlenT hlenT' hpT ⟨i, hlen ▸ h1⟩
  have e1 : (finCongr hlen).symm ⟨i, hlen ▸ h1⟩ = ⟨i, h1⟩ := rfl
  have e2 : (finCongr hlen').symm ⟨i, hlen ▸ h1⟩ = ⟨i, h2⟩ := rfl
  have e3 : ((tl.map Rect.transpose).get ((finCongr hlenT).symm ⟨i, hlen ▸ h1⟩)) = (tl.get ⟨i, h1⟩).transpose := by
    simp
  have e4 : ((tl'.map Rect.transpose).get ((finCongr hlenT').symm ⟨i, hlen ▸ h1⟩)) = (tl'.get ⟨i, h2⟩).transpose := by
    simp
  rw [e1, e2] at A
  rw [e3, e4] at B
  exact Rect.ext B.1 A.1 A.2.1 A.2.2

/-- The unit square has finitely many similar tilings of a given proportion with a given number of tiles. -/
theorem finite_similarTilings_of (n : ℕ) (x : ℝ) :
    {tl : List Rect | tl.length = n ∧ IsSimilarTiling x (Rect.main 1 1) tl}.Finite := by
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (β := Pair n × Pair n)
    (fun tl => (heightPair x tl.1 tl.2.1 tl.2.2.toIsTiling,
      heightPair x (tl.1.map Rect.transpose) (by rw [List.length_map]; exact tl.2.1)
        tl.2.2.transpose.toIsTiling)) ?_
  rintro ⟨tl, hlen, h⟩ ⟨tl', hlen', h'⟩ heq
  simp only [Prod.mk.injEq] at heq
  exact Subtype.ext (h.eq_of_heightPair_eq h' hlen hlen' h.transpose h'.transpose _ _ heq.1 heq.2)

/-- The unit square has finitely many similar tilings with a given number of tiles, as lists of rectangles. -/
theorem finite_similarTilings (n : ℕ) :
    {tl : List Rect | tl.length = n ∧ ∃ x, IsSimilarTiling x (Rect.main 1 1) tl}.Finite := by
  refine ((finite_achievable n).biUnion fun x _ => finite_similarTilings_of n x).subset ?_
  rintro tl ⟨hlen, x, h⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact ⟨x, ⟨tl, hlen, h⟩, hlen, h⟩

/-- The unit square has finitely many similar tilings with a given number of tiles, as sets of rectangles. -/
theorem finite_similarTilingSets (n : ℕ) :
    {S : Set Rect | ∃ tl : List Rect, (tl.length = n ∧ ∃ x, IsSimilarTiling x (Rect.main 1 1) tl) ∧
      {t | t ∈ tl} = S}.Finite :=
  (finite_similarTilings n).image fun tl => {t | t ∈ tl}

end Rectiling
