/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Hall

/-!
# Local prerequisites for prime-leaf planarity

These statements expose the connectivity supplied by `NoSmallSep`. They do not
construct a rotation system; the planarity of prime pieces is proved in `Kuratowski.lean`.
(This is the supplied `PrimeLeafAttack.lean`, stated for an arbitrary `DecidableEq` instance.)
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

/-- Deleting at most two vertices from a prime piece leaves a connected nonempty
remainder, whenever the remainder is nonempty. -/
theorem NoSmallSep.connSet_sdiff {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S Z : Finset V} (h : NoSmallSep G S) (hZS : Z ⊆ S) (hZ : Z.card ≤ 2)
    (hne : (S \ Z).Nonempty) : ConnSet G ↑(S \ Z) := by
  classical
  refine ⟨hne, ?_⟩
  intro x hx y hy
  let W := S \ Z
  let C := reachIn G W x
  let A := C ∪ Z
  let B := (W \ C) ∪ Z
  have hCW : C ⊆ W := reachIn_sub W x
  have hxC : x ∈ C := mem_reachIn_self hx
  have hxZ : x ∉ Z := (Finset.mem_sdiff.1 hx).2
  have hcover : A ∪ B = S := by
    ext v
    simp only [A, B, W, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((hvC | hvZ) | (⟨⟨hvS, _⟩, _⟩ | hvZ))
      · exact (Finset.mem_sdiff.1 (hCW hvC)).1
      · exact hZS hvZ
      · exact hvS
      · exact hZS hvZ
    · intro hvS
      by_cases hvZ : v ∈ Z
      · exact Or.inl (Or.inr hvZ)
      · by_cases hvC : v ∈ C
        · exact Or.inl (Or.inl hvC)
        · exact Or.inr (Or.inl ⟨⟨hvS, hvZ⟩, hvC⟩)
  have hinter : A ∩ B ⊆ Z := by
    intro v hv
    obtain ⟨hvA, hvB⟩ := Finset.mem_inter.1 hv
    by_contra hvZ
    have hvC := (Finset.mem_union.1 hvA).resolve_right hvZ
    have hvNC := (Finset.mem_sdiff.1 ((Finset.mem_union.1 hvB).resolve_right hvZ)).2
    exact hvNC hvC
  have hcross : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ G.Adj u v := by
    intro u hu huB v hv hvA huv
    have huZ : u ∉ Z := fun huZ => huB (Finset.mem_union_right _ huZ)
    have hvZ : v ∉ Z := fun hvZ => hvA (Finset.mem_union_right _ hvZ)
    have huC := (Finset.mem_union.1 hu).resolve_right huZ
    have hvWC := (Finset.mem_union.1 hv).resolve_right hvZ
    have hvC := reachIn_closed huC (Finset.mem_sdiff.1 hvWC).1 huv
    exact (Finset.mem_sdiff.1 hvWC).2 hvC
  rcases h A B hcover ((Finset.card_le_card hinter).trans hZ) hcross with hAB | hBA
  · have hxB := hAB (Finset.mem_union_left _ hxC)
    rcases Finset.mem_union.1 hxB with hxWC | hxZ'
    · exact ((Finset.mem_sdiff.1 hxWC).2 hxC).elim
    · exact (hxZ hxZ').elim
  · have hyC : y ∈ C := by
      by_contra hyC
      have hyB : y ∈ B := Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hy, hyC⟩)
      rcases Finset.mem_union.1 (hBA hyB) with hyC' | hyZ
      · exact hyC hyC'
      · exact (Finset.mem_sdiff.1 hy).2 hyZ
    exact (mem_reachIn.1 hyC).2

/-- The converse connects the separation certificate with deletion connectivity.
The empty remainder is excluded because `ConnSet` includes nonemptiness. -/
theorem noSmallSep_of_connSet_sdiff {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V}
    (h : ∀ Z : Finset V, Z ⊆ S → Z.card ≤ 2 →
      (S \ Z).Nonempty → ConnSet G ↑(S \ Z)) : NoSmallSep G S := by
  classical
  intro A B hcover hcard hcross
  by_contra hn
  have hAB : ¬ A ⊆ B := fun hab => hn (Or.inl hab)
  have hBA : ¬ B ⊆ A := fun hba => hn (Or.inr hba)
  obtain ⟨x, hxA, hxB⟩ := Finset.not_subset.1 hAB
  obtain ⟨y, hyB, hyA⟩ := Finset.not_subset.1 hBA
  have hZS : A ∩ B ⊆ S := by
    intro z hz
    rw [← hcover]
    exact Finset.mem_union_left _ (Finset.mem_inter.1 hz).1
  have hxW : x ∈ S \ (A ∩ B) := by
    rw [← hcover]
    exact Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ hxA,
      fun hx => hxB (Finset.mem_inter.1 hx).2⟩
  have hyW : y ∈ S \ (A ∩ B) := by
    rw [← hcover]
    exact Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hyB,
      fun hy => hyA (Finset.mem_inter.1 hy).1⟩
  have hxy := (h (A ∩ B) hZS hcard ⟨x, hxW⟩).2 x hxW y hyW
  obtain ⟨u, v, _, huW, huA, hvW, hvA, huv⟩ :=
    hxy.exit (P := (↑A : Set V)) hxA hyA
  have huB : u ∉ B := by
    intro huB
    exact (Finset.mem_sdiff.1 huW).2 (Finset.mem_inter.2 ⟨huA, huB⟩)
  have hvB : v ∈ B := by
    have hvS := (Finset.mem_sdiff.1 hvW).1
    rw [← hcover] at hvS
    exact (Finset.mem_union.1 hvS).resolve_left hvA
  exact hcross u huA huB v hvB hvA huv

end LeanPool.K5MinorFreeChoosability
