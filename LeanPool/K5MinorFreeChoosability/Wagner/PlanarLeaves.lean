/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.DecompositionConverse
public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-!
# Planar-leaf form of the decomposition: the remaining open obligation, made precise

`exists_k33Decomp` proves, from standard `K_{3,3}`-minor exclusion, a decomposition whose leaves
are small (order `≤ 5`) or *prime* (no `K_5` minor, no `K_{3,3}` minor, no separation of order
`≤ 2`).  The planar-leaf form requested by Li–Wang's citation of Wagner additionally needs every
prime leaf to be planar in the combinatorial embedding model `IsPlanar`.  That is the reverse
direction of Wagner's planarity criterion (Kuratowski) for graphs without `≤ 2`-separations and
is **not** proved here.

This file is **conditional scaffolding**: it isolates that obligation as the explicit hypothesis
`PrimeLeafPlanarity H` and shows that it is the only missing step (`K33Decomp.toPlanar`,
`exists_k33DecompPlanar_of_primeLeafPlanarity`).  Nothing proved unconditionally elsewhere
depends on this file.

Round-six update: the obligation is now discharged unconditionally in `Wagner/Kuratowski`
(`primeLeafPlanarity`, `exists_k33DecompPlanar`); this file is kept unchanged as the
conditional interface.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

/-- Decomposition certificate with **planar** leaves: leaves are small (`|S| ≤ 5`) and
`K_{3,3}`-minor-free, or planar in the embedding model; internal nodes are retained-clique
gluings of order at most two with no cross edges, exactly as in `K33Decomp`. -/
inductive K33DecompPlanar (H : SimpleGraph V) : Finset V → Prop
  | small {S : Finset V} : S.card ≤ 5 → K33MinorFree (restrict H ↑S) → K33DecompPlanar H S
  | planar {S : Finset V} : IsPlanar (restrict H ↑S) → K33DecompPlanar H S
  | glue {A B : Finset V} : ¬ A ⊆ B → ¬ B ⊆ A → (A ∩ B).card ≤ 2 →
      (∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → H.Adj u v) →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) →
      K33DecompPlanar H A → K33DecompPlanar H B → K33DecompPlanar H (A ∪ B)

/-- Unconditional easy direction: a finite graph with a planar-leaf certificate on `S` is
`K_{3,3}`-minor-free on `S`. -/
theorem k33MinorFree_of_k33DecompPlanar [Finite V] {H : SimpleGraph V} {S : Finset V}
    (hd : K33DecompPlanar H S) : K33MinorFree (restrict H ↑S) := by
  induction hd with
  | small _ h => exact h
  | planar h => exact k33MinorFree_of_isPlanar h
  | glue _ _ hcard hcl hnc _ _ ihA ihB => exact k33MinorFree_restrict_union hcard hcl hnc ihA ihB

/-- The **open obligation** (Kuratowski/Wagner for prime pieces), stated for one graph `H`:
every induced piece of `H` with no `K_5` minor, no `K_{3,3}` minor and no separation of order
`≤ 2` is planar.  This is a hypothesis-carrying `Prop`, not an assumption of the project. -/
def PrimeLeafPlanarity (H : SimpleGraph V) : Prop :=
  ∀ S : Finset V, K5MinorFree (restrict H ↑S) → K33MinorFree (restrict H ↑S) →
    NoSmallSep (restrict H ↑S) S → IsPlanar (restrict H ↑S)

/-- Conditional: under `PrimeLeafPlanarity H`, a `K33Decomp` certificate is a planar-leaf
certificate. -/
theorem K33Decomp.toPlanar {H : SimpleGraph V} (hP : PrimeLeafPlanarity H) {S : Finset V}
    (hd : K33Decomp H S) : K33DecompPlanar H S := by
  induction hd with
  | small hS h => exact .small hS h
  | prime h5 h33 hsep => exact .planar (hP _ h5 h33 hsep)
  | glue hAB hBA hcard hcl hnc _ _ ihA ihB => exact .glue hAB hBA hcard hcl hnc ihA ihB

/-- Conditional planar-leaf Wagner decomposition: if the completion produced by
`exists_k33Decomp` satisfies `PrimeLeafPlanarity` — in particular, if the open
Kuratowski/Wagner step is supplied for all graphs on `V` — then a finite `K_{3,3}`-minor-free
graph is a spanning subgraph of a planar-leaf certificate.  **Conditional; not a closure of the
planar-leaf form.** -/
theorem exists_k33DecompPlanar_of_primeLeafPlanarity [Fintype V]
    (hP : ∀ H : SimpleGraph V, PrimeLeafPlanarity H) (G : SimpleGraph V) (hG : K33MinorFree G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ K33DecompPlanar H Finset.univ := by
  obtain ⟨H, hGH, hd⟩ := exists_k33Decomp G hG
  exact ⟨H, hGH, hd.toPlanar (hP H)⟩

end LeanPool.K5MinorFreeChoosability
