/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Hall

/-!
# Contracting an edge inside a fixed vertex type

`contractGraph G x y` is the graph `G / xy` realised on the same vertex type: the vertex `x`
represents the contracted edge and receives the neighbours of `y`, while `y` becomes isolated.
Minors of the contraction are minors of `G` (`isMinor_of_isMinor_contractGraph`).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- The contraction `G / xy` on the vertex type of `G`: `x` is the contracted vertex and `y` is
isolated. -/
def contractGraph (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ≠ y ∧ v ≠ y ∧ (G.Adj u v ∨ (u = x ∧ G.Adj y v) ∨ (v = x ∧ G.Adj u y))
  symm := ⟨fun u v ⟨h1, h2, h3, h4⟩ => ⟨Ne.symm h1, h3, h2, by
    rcases h4 with h | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h, h'.symm⟩)
    · exact Or.inr (Or.inl ⟨h, h'.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G : SimpleGraph V} {x y : V}

theorem contractGraph_adj {u v : V} : (contractGraph G x y).Adj u v ↔
    u ≠ v ∧ u ≠ y ∧ v ≠ y ∧ (G.Adj u v ∨ (u = x ∧ G.Adj y v) ∨ (v = x ∧ G.Adj u y)) :=
  Iff.rfl

theorem contractGraph_adj_of_ne {u v : V} (hux : u ≠ x) (hvx : v ≠ x) (huy : u ≠ y)
    (hvy : v ≠ y) : (contractGraph G x y).Adj u v ↔ G.Adj u v := by
  rw [contractGraph_adj]
  constructor
  · rintro ⟨-, -, -, h | ⟨h, -⟩ | ⟨h, -⟩⟩
    · exact h
    · exact absurd h hux
    · exact absurd h hvx
  · intro h
    exact ⟨h.ne, huy, hvy, Or.inl h⟩

theorem contractGraph_adj_x {v : V} (hxy : x ≠ y) :
    (contractGraph G x y).Adj x v ↔ v ≠ x ∧ v ≠ y ∧ (G.Adj x v ∨ G.Adj y v) := by
  rw [contractGraph_adj]
  constructor
  · rintro ⟨h1, -, h3, h | ⟨-, h⟩ | ⟨h, -⟩⟩
    · exact ⟨Ne.symm h1, h3, Or.inl h⟩
    · exact ⟨Ne.symm h1, h3, Or.inr h⟩
    · exact absurd h.symm h1
  · rintro ⟨h1, h2, h | h⟩
    · exact ⟨Ne.symm h1, hxy, h2, Or.inl h⟩
    · exact ⟨Ne.symm h1, hxy, h2, Or.inr (Or.inl ⟨rfl, h⟩)⟩

theorem contractGraph_not_adj_y (v : V) : ¬ (contractGraph G x y).Adj y v := fun h => h.2.1 rfl

theorem contractGraph_support [DecidableEq V] {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hxy : G.Adj x y)
    {u v : V} (h : (contractGraph G x y).Adj u v) : u ∈ S.erase y := by
  obtain ⟨-, huy, -, h | ⟨h, -⟩ | ⟨-, h⟩⟩ := h
  · exact Finset.mem_erase.2 ⟨huy, hS u v h⟩
  · exact Finset.mem_erase.2 ⟨huy, h ▸ hS x y hxy⟩
  · exact Finset.mem_erase.2 ⟨huy, hS u y h⟩

/-- Minors of the contraction are minors of the original graph. -/
theorem isMinor_of_isMinor_contractGraph {W : Type*} {K : SimpleGraph W}
    (hK : ∀ w, ∃ w', K.Adj w w') (hxy : G.Adj x y) (h : IsMinor K (contractGraph G x y)) :
    IsMinor K G := by
  classical
  have hne : x ≠ y := hxy.ne
  let φ : V → Finset V := fun v => if v = x then {x, y} else {v}
  have hφx : φ x = {x, y} := by simp [φ]
  have hφ : ∀ v, v ≠ x → φ v = {v} := fun v hv => by simp [φ, hv]
  have hmem : ∀ v, v ∈ φ v := fun v => by
    by_cases hv : v = x
    · subst hv; simp [hφx]
    · simp [hφ v hv]
  refine isMinor_of_transport hK {v | v ≠ y}
    (fun u v (huv : (contractGraph G x y).Adj u v) => huv.2.1) φ (fun v _ => ?_)
    (fun u hu v hv huv => ?_) (fun u v huv => ?_) h
  · by_cases hv : v = x
    · subst hv
      rw [hφx, Finset.coe_insert, Finset.coe_singleton]
      exact (connSet_singleton G y).insert_adj (Set.mem_singleton y) hxy
    · rw [hφ v hv, Finset.coe_singleton]; exact connSet_singleton G v
  · simp only [Set.mem_ofPred_eq] at hu hv
    by_cases hux : u = x
    · subst hux
      rw [hφx, hφ v (Ne.symm huv)]
      simp [Ne.symm huv, hv]
    · by_cases hvx : v = x
      · subst hvx
        rw [hφx, hφ u hux]
        simp [hux, hu]
      · rw [hφ u hux, hφ v hvx]; simpa using huv
  · obtain ⟨-, -, -, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := huv
    · exact ⟨u, hmem u, v, hmem v, h⟩
    · refine ⟨y, ?_, v, hmem v, h2⟩
      rw [h1, hφx]; simp
    · refine ⟨u, hmem u, y, ?_, h2⟩
      rw [h1, hφx]; simp

theorem k5MinorFree_contractGraph (hxy : G.Adj x y) (h : K5MinorFree G) :
    K5MinorFree (contractGraph G x y) := by
  unfold K5MinorFree at h ⊢
  rw [cliqueMinorFree_iff_not_isMinor] at h ⊢
  exact fun h' => h (isMinor_of_isMinor_contractGraph top_five_hasNeighbor hxy h')

theorem k33MinorFree_contractGraph (hxy : G.Adj x y) (h : K33MinorFree G) :
    K33MinorFree (contractGraph G x y) :=
  fun h' => h (isMinor_of_isMinor_contractGraph K33_hasNeighbor hxy h')

end LeanPool.K5MinorFreeChoosability
