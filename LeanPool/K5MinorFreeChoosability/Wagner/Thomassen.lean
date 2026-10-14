/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Uncontract

/-!
# Uncontracting an edge in the good case

After `exists_planeMap_split`, the edges from `y` to the (at most two) common neighbours of `x`
and `y` at the ends of the `y`-interval are added back inside faces (`flank_first`,
`flank_last`).  `isPlanar_of_good` is the resulting uncontraction step of Thomassen's proof.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*}

/-- Planarity only depends on the adjacency relation. -/
theorem isPlanar_congr {G G' : SimpleGraph V} (h : ∀ a b, G.Adj a b ↔ G'.Adj a b)
    (hG : IsPlanar G) : IsPlanar G' := by
  have : G = G' := by
    ext a b
    exact h a b
  exact this ▸ hG

/-- A graph with one edge added. -/
def addEdgeGraph (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (a ≠ b ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)))
  symm := ⟨fun a b h => by
    rcases h with h | ⟨hne, h | h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, Or.inr ⟨h.2, h.1⟩⟩
    · exact Or.inr ⟨hne.symm, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨fun a h => by
    rcases h with h | ⟨hne, -⟩
    · exact G.loopless.irrefl a h
    · exact hne rfl⟩

theorem addEdgeGraph_adj {G : SimpleGraph V} {u v : V} (huv : u ≠ v) (a b : V) :
    (addEdgeGraph G u v).Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨by rw [h.1, h.2]; exact huv, Or.inl h⟩
    · exact Or.inr ⟨by rw [h.1, h.2]; exact huv.symm, Or.inr h⟩

variable [Finite V] [DecidableEq V]

omit [DecidableEq V] in
/-- Adding the edge from `y` to the neighbour `ws` of `x` that precedes `y` around `x`. -/
theorem flank_first {G G' : SimpleGraph V} (N : PlaneMap G) {x y ws wl : V}
    (hadj : ∀ a b, G'.Adj a b ↔ G.Adj a b ∨ (a = y ∧ b = ws) ∨ (a = ws ∧ b = y))
    (hny : ¬ G.Adj y ws) (hxy : G.Adj x y) (hxs : G.Adj x ws)
    (h1 : ∀ d : G.Dart, d.toProd = (x, ws) → (N.rot d).toProd = (x, y))
    (h2 : ∀ d : G.Dart, d.toProd = (x, y) → (N.rot d).toProd = (x, wl)) :
    ∃ N' : PlaneMap G', ∀ d : G'.Dart, d.toProd = (x, y) → (N'.rot d).toProd = (x, wl) := by
  classical
  let b : G.Dart := ⟨(x, y), hxy⟩
  let a : G.Dart := b.symm
  let g : G.Dart := ⟨(x, ws), hxs⟩
  have hgb : N.rot g = b := (SimpleGraph.Dart.ext_iff _ _).2 (h1 g rfl)
  have hp : (N.rot a).fst = y := N.isRotationSystem.fst_apply a
  have hf : SameCycle N.facePerm (N.rot a) g.symm := by
    refine SameCycle.symm ⟨2, ?_⟩
    rw [zpow_two, Perm.mul_apply, PlaneMap.facePerm_apply, PlaneMap.facePerm_apply,
      SimpleGraph.Dart.symm_symm, hgb]
  obtain ⟨N', hN'⟩ := exists_planeMap_addEdge N hadj hny (N.rot a) g.symm hp rfl hf
  refine ⟨N', fun d hd => ?_⟩
  have hd' : d = inclDart hadj b := (SimpleGraph.Dart.ext_iff _ _).2 hd
  have hba : b ≠ N.rot⁻¹ (N.rot a) := by
    rw [show N.rot⁻¹ (N.rot a) = a by simp]
    exact fun e => hxy.ne (congrArg (fun z : G.Dart => z.fst) e)
  have hbq : b ≠ N.rot⁻¹ g.symm := by
    intro e
    have := congrArg (fun z : G.Dart => z.fst) e
    simp only [N.fst_rot_inv] at this
    exact hxs.ne this
  rw [hd', hN' b hba hbq]
  exact h2 b rfl

omit [DecidableEq V] in
/-- Adding the edge from `y` to the neighbour `wl` of `x` that follows `y` around `x`. -/
theorem flank_last {G G' : SimpleGraph V} (N : PlaneMap G) {x y wl : V}
    (hadj : ∀ a b, G'.Adj a b ↔ G.Adj a b ∨ (a = y ∧ b = wl) ∨ (a = wl ∧ b = y))
    (hny : ¬ G.Adj y wl) (hxy : G.Adj x y) (hxl : G.Adj x wl)
    (h2 : ∀ d : G.Dart, d.toProd = (x, y) → (N.rot d).toProd = (x, wl)) :
    IsPlanar G' := by
  classical
  let b : G.Dart := ⟨(x, y), hxy⟩
  let g : G.Dart := ⟨(x, wl), hxl⟩
  have hbg : N.rot b = g := (SimpleGraph.Dart.ext_iff _ _).2 (h2 b rfl)
  have hq : (N.rot g.symm).fst = wl := N.isRotationSystem.fst_apply g.symm
  have hf : SameCycle N.facePerm b.symm (N.rot g.symm) := by
    refine ⟨2, ?_⟩
    rw [zpow_two, Perm.mul_apply, PlaneMap.facePerm_apply, PlaneMap.facePerm_apply,
      SimpleGraph.Dart.symm_symm, hbg]
  obtain ⟨N', -⟩ := exists_planeMap_addEdge N hadj hny b.symm (N.rot g.symm) rfl hq hf
  exact ⟨N'⟩

section Good

variable {H : SimpleGraph V} {x y : V} (hxy : H.Adj x y) (M : PlaneMap (contractGraph H x y))
  (e0 : (contractGraph H x y).Dart) (he0 : e0.fst = x)
include hxy he0

omit [DecidableEq V] in
/-- **Uncontraction in the good case.**  If, around the contracted vertex, the neighbours of `y`
that are not neighbours of `x` form one interval, all other neighbours are neighbours of `x`, and
common neighbours of `x` and `y` occur only at the two ends of the interval, then `H` is
planar. -/
theorem isPlanar_of_good {s ℓ : ℕ} (hℓ : ℓ + 1 < M.rper e0)
    (hA : ∀ t, 1 ≤ t → t ≤ ℓ → ¬ H.Adj x (M.rd e0 (s + t)).snd)
    (hB : ∀ t, ℓ + 1 ≤ t → t ≤ M.rper e0 → H.Adj x (M.rd e0 (s + t)).snd ∧
      (H.Adj y (M.rd e0 (s + t)).snd → t = ℓ + 1 ∨ t = M.rper e0)) : IsPlanar H := by
  classical
  obtain ⟨P, hP1, hP2⟩ :=
    exists_planeMap_split hxy M e0 he0 hℓ hA (fun t h1 h2 => (hB t h1 h2).1)
  set k := M.rper e0 with hk
  set ws := (M.rd e0 s).snd with hws
  set wl := (M.rd e0 (s + ℓ + 1)).snd with hwl
  have hrdfst : ∀ j, (M.rd e0 j).fst = x := fun j => by rw [M.rd_fst, he0]
  have hwy : ∀ j, (M.rd e0 j).snd ≠ y := rd_snd_ne_y M e0
  have hrds : M.rd e0 (s + k) = M.rd e0 s := M.rd_add_rper e0 s
  have hXs : H.Adj x ws := by
    have := (hB k (by omega) le_rfl).1
    rwa [hrds] at this
  have hXl : H.Adj x wl := by
    have := (hB (ℓ + 1) le_rfl (by omega)).1
    rwa [← add_assoc] at this
  have hsl : ws ≠ wl := by
    intro e
    refine M.rd_injOn e0 (i := s) (j := s + ℓ + 1) (by omega) (by omega) ?_
    exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext (by rw [hrdfst, hrdfst]) e)
  have hwin : ∀ v, (contractGraph H x y).Adj x v →
      ∃ t, 1 ≤ t ∧ t ≤ k ∧ (M.rd e0 (s + t)).snd = v := by
    intro v hv
    obtain ⟨i, -, hi⟩ := M.exists_rd_eq e0 (d := ⟨(x, v), hv⟩) he0.symm
    obtain ⟨t, ht, ht'⟩ := M.exists_window e0 (s + 1) i
    refine ⟨t + 1, by omega, by omega, ?_⟩
    rw [← add_assoc, add_right_comm, ht', hi]
  have hkey : ∀ v, H.Adj y v → H.Adj x v → v = ws ∨ v = wl := by
    intro v hyv hxv
    have hv : (contractGraph H x y).Adj x v :=
      (contractGraph_adj_x hxy.ne).2 ⟨hxv.ne.symm, hyv.ne.symm, Or.inl hxv⟩
    obtain ⟨t, ht1, htk, rfl⟩ := hwin v hv
    by_cases htl : t ≤ ℓ
    · exact absurd hxv (hA t ht1 htl)
    · rcases (hB t (by omega) htk).2 hyv with h | h
      · right
        rw [h, ← add_assoc]
      · left
        rw [h, hrds]
  have hsplit : ∀ a b, H.Adj a b ↔ (splitGraph H x y).Adj a b ∨
      (H.Adj y ws ∧ ((a = y ∧ b = ws) ∨ (a = ws ∧ b = y))) ∨
      (H.Adj y wl ∧ ((a = y ∧ b = wl) ∨ (a = wl ∧ b = y))) := by
    intro a b
    constructor
    · intro h
      by_cases hs : (splitGraph H x y).Adj a b
      · exact Or.inl hs
      right
      rw [splitGraph_adj] at hs
      push Not at hs
      by_cases ha : a = y ∧ H.Adj x b
      · obtain ⟨rfl, hxb⟩ := ha
        rcases hkey b h hxb with rfl | rfl
        · exact Or.inl ⟨h, Or.inl ⟨rfl, rfl⟩⟩
        · exact Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩
      · have hb : b = y ∧ H.Adj x a := by
          by_contra hb
          exact hb (hs h (fun h1 h2 => ha ⟨h1, h2⟩))
        obtain ⟨rfl, hxa⟩ := hb
        rcases hkey a h.symm hxa with rfl | rfl
        · exact Or.inl ⟨h.symm, Or.inr ⟨rfl, rfl⟩⟩
        · exact Or.inr ⟨h.symm, Or.inr ⟨rfl, rfl⟩⟩
    · rintro (h | ⟨h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
      · exact h.1
      · exact h
      · exact h.symm
      · exact h
      · exact h.symm
  have sxy : (splitGraph H x y).Adj x y := ⟨hxy, fun h => hxy.ne h.1, fun h => H.irrefl h.2⟩
  have sxs : (splitGraph H x y).Adj x ws := ⟨hXs, fun h => hxy.ne h.1, fun h => hwy s h.1⟩
  have sxl : (splitGraph H x y).Adj x wl := ⟨hXl, fun h => hxy.ne h.1, fun h => hwy _ h.1⟩
  have nys : ¬ (splitGraph H x y).Adj y ws := fun h => h.2.1 ⟨rfl, hXs⟩
  have nyl : ¬ (splitGraph H x y).Adj y wl := fun h => h.2.1 ⟨rfl, hXl⟩
  by_cases Bs : H.Adj y ws <;> by_cases Bl : H.Adj y wl
  · -- both flank edges are present
    have hadj1 := addEdgeGraph_adj (G := splitGraph H x y) (hwy s).symm
    obtain ⟨N1, hN1⟩ := flank_first P hadj1 nys sxy sxs hP1 hP2
    refine flank_last N1 (G' := H) (fun a b => ?_) ?_ (Or.inl sxy) (Or.inl sxl) hN1
    · rw [hsplit, hadj1]
      simp only [Bs, Bl, true_and]
      tauto
    · rw [hadj1]
      rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
      · exact nyl h
      · exact hsl h.symm
      · exact hwy s h.symm
  · obtain ⟨N1, -⟩ := flank_first P (G' := H) (fun a b => by
      rw [hsplit]; simp only [Bs, Bl, true_and, false_and, or_false]) nys sxy sxs hP1 hP2
    exact ⟨N1⟩
  · exact flank_last P (G' := H) (fun a b => by
      rw [hsplit]; simp only [Bs, Bl, true_and, false_and, false_or]) nyl sxy sxl hP2
  · exact isPlanar_congr (fun a b => by
      rw [hsplit]; simp only [Bs, Bl, false_and, or_false]) ⟨P⟩

end Good

end LeanPool.K5MinorFreeChoosability
