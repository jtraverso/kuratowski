/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Basic

/-!
# Candidate contracts for finite list colouring and complete graph minors

These definitions have not been compiled locally. They use native graph and
colouring objects, and the standard connected branch-set meaning of a minor.
Reuse a matching existing minor API if one is found, with proved equivalence.
The completion task must prove results, not change these meanings to make
the goals tautological or conditional on an assumed colouring.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V C : Type*}

/-- A native proper colouring choosing its colour from the assigned finite list. -/
def ListColourable (G : SimpleGraph V) (L : V → Finset C) : Prop :=
  ∃ c : G.Coloring C, ∀ v, c v ∈ L v

/-- Choosability for all lists over a specified, arbitrary colour type. -/
def ChoosableWith (G : SimpleGraph V) (C : Type*) (k : ℕ) : Prop :=
  ∀ L : V → Finset C, (∀ v, k ≤ (L v).card) → ListColourable G L

/-- A complete minor model consists of disjoint, nonempty, connected branch sets
with an edge between every pair of different branch sets. -/
structure CliqueMinorModel (G : SimpleGraph V) (k : ℕ) where
  branch : Fin k → Finset V
  branch_nonempty : ∀ i, (branch i).Nonempty
  branch_connected : ∀ i, (G.induce (↑(branch i) : Set V)).Connected
  branch_disjoint : ∀ i j, i ≠ j → Disjoint (branch i) (branch j)
  branch_adjacent : ∀ i j, i ≠ j →
    ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v

/-- Standard exclusion of a complete minor, not a decomposition certificate. -/
def CliqueMinorFree (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ Nonempty (CliqueMinorModel G k)

end LeanPool.K5MinorFreeChoosability
