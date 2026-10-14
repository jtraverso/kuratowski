/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Minors and topological minors

* `MinorModel G H`: a branch-set model of `H` as a minor of `G` (disjoint, nonempty, connected
  branch sets, adjacent branch sets for adjacent vertices of `H`);
* `TopologicalMinorModel G H`: a subdivision of `H` inside `G`: an injective choice of branch
  vertices and, for every ordered pair of adjacent vertices of `H`, a path of `G` between their
  branch vertices that meets the branch vertices only at its ends, paths of different edges of
  `H` meeting only at branch vertices.
-/

@[expose] public section

open SimpleGraph

namespace Kuratowski

variable {V W : Type*}

/-- A branch-set model of `H` as a minor of `G`: disjoint, nonempty, connected branch sets, one
for every vertex of `H`, with an edge of `G` between the branch sets of adjacent vertices. -/
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v

/-- `H` is a minor of `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)

/-- A subdivision of `H` in `G`: distinct branch vertices, and for every ordered pair of adjacent
vertices of `H` a path of `G` joining their branch vertices, which contains no other branch
vertex; paths of different edges of `H` meet only at branch vertices. -/
structure TopologicalMinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  vertex : W ↪ V
  path : ∀ w w', H.Adj w w' → G.Walk (vertex w) (vertex w')
  path_isPath : ∀ w w' (h : H.Adj w w'), (path w w' h).IsPath
  path_branch : ∀ w w' (h : H.Adj w w') (u : W), vertex u ∈ (path w w' h).support →
    u = w ∨ u = w'
  path_disjoint : ∀ w₁ w₁' (h₁ : H.Adj w₁ w₁') w₂ w₂' (h₂ : H.Adj w₂ w₂'),
    s(w₁, w₁') ≠ s(w₂, w₂') → ∀ v ∈ (path w₁ w₁' h₁).support, v ∈ (path w₂ w₂' h₂).support →
      v ∈ Set.range vertex

/-- `H` is a topological minor of `G`: `G` contains a subdivision of `H`. -/
def IsTopologicalMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (TopologicalMinorModel G H)

end Kuratowski
