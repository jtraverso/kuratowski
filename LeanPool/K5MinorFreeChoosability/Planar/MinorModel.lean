/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Reach

/-!
# General branch-set minor models

`MinorModel G H` is the standard branch-set witness that `H` is a minor of `G`: disjoint,
nonempty, connected branch sets of `G`, one per vertex of `H`, such that adjacent vertices of
`H` have adjacent branch sets.  Only the adjacencies of `H` are required; further edges of `G`
between branch sets are allowed.

* `CliqueMinorModel.toMinorModel`, `MinorModel.toCliqueMinorModel` and
  `cliqueMinorFree_iff_not_isMinor`: a complete minor model in the sense of
  `CliqueMinorModel` is exactly a minor model of the complete graph `⊤ : SimpleGraph (Fin k)`.
* `K33 = completeBipartiteGraph (Fin 3) (Fin 3)`; a `K33` minor model requires only the nine
  adjacencies between the two sides, *not* six pairwise adjacent branch sets.
* `MinorModel.ofIso`: isomorphic graphs are minors of each other.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V W : Type*}

/-- A branch-set model of `H` as a minor of `G`. -/
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v

/-- `H` is a minor of `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)

/-- The complete bipartite graph `K_{3,3}`, with sides `Sum.inl` and `Sum.inr`. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

instance : DecidableRel K33.Adj := fun u v =>
  decidable_of_iff ((u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft)) Iff.rfl

/-- `G` has no `K_{3,3}` minor. -/
def K33MinorFree (G : SimpleGraph V) : Prop := ¬ IsMinor K33 G

variable {G : SimpleGraph V} {k : ℕ}

/-- A complete minor model is a minor model of the complete graph. -/
def CliqueMinorModel.toMinorModel (M : CliqueMinorModel G k) :
    MinorModel G (⊤ : SimpleGraph (Fin k)) where
  branch := M.branch
  branch_nonempty := M.branch_nonempty
  branch_connected := M.branch_connected
  branch_disjoint := M.branch_disjoint
  branch_adjacent i j h := M.branch_adjacent i j h

/-- A minor model of the complete graph is a complete minor model. -/
def MinorModel.toCliqueMinorModel (M : MinorModel G (⊤ : SimpleGraph (Fin k))) :
    CliqueMinorModel G k where
  branch := M.branch
  branch_nonempty := M.branch_nonempty
  branch_connected := M.branch_connected
  branch_disjoint := M.branch_disjoint
  branch_adjacent i j h := M.branch_adjacent i j h

theorem cliqueMinorFree_iff_not_isMinor :
    CliqueMinorFree G k ↔ ¬ IsMinor (⊤ : SimpleGraph (Fin k)) G :=
  ⟨fun h ⟨M⟩ => h ⟨M.toCliqueMinorModel⟩, fun h ⟨M⟩ => h ⟨M.toMinorModel⟩⟩

/-- An isomorphism gives a minor model with singleton branch sets. -/
def MinorModel.ofIso {H : SimpleGraph W} (e : H ≃g G) : MinorModel G H where
  branch w := {e w}
  branch_nonempty w := Finset.singleton_nonempty _
  branch_connected w := by
    rw [← connSet_iff_induce_connected]
    simpa using connSet_singleton G (e w)
  branch_disjoint w w' h := by
    simpa using fun h' => h (e.injective h')
  branch_adjacent w w' h := ⟨e w, by simp, e w', by simp, e.map_adj_iff.2 h⟩

namespace MinorModel

variable {H : SimpleGraph W} (M : MinorModel G H)

theorem eq_of_mem {w w' : W} {v : V} (hv : v ∈ M.branch w) (hv' : v ∈ M.branch w') :
    w = w' := by
  by_contra h
  exact Finset.disjoint_left.1 (M.branch_disjoint w w' h) hv hv'

theorem connSet (w : W) : ConnSet G ↑(M.branch w) :=
  (connSet_iff_induce_connected _ _).2 (M.branch_connected w)

include M in
/-- The vertex type of a minor of a finite graph is finite. -/
theorem finite_of_finite [Finite V] : Finite W := by
  classical
  refine Finite.of_injective (fun w => (M.branch_nonempty w).choose) (fun w w' h => ?_)
  have h1 := (M.branch_nonempty w).choose_spec
  have h2 := (M.branch_nonempty w').choose_spec
  simp only at h
  rw [h] at h1
  exact M.eq_of_mem h1 h2

end MinorModel

end LeanPool.K5MinorFreeChoosability
