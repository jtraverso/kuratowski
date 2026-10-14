/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.MinorModel
public import LeanPool.K5MinorFreeChoosability.Minor

/-!
# Separations, `K_{3,3}` minor models and transport

Basic tools for the structure theory of `K_{3,3}`-minor-free graphs.

* `Touch G X Y`: some edge of `G` joins `X` and `Y`.
* `NoSmallSep G S`: the vertex set `S` has no separation `(A, B)` of order at most two with
  both private parts nonempty (for graphs whose edges lie inside `S`, together with
  `6 ≤ S.card` this is the usual notion of `3`-connectivity).
* `isMinor_K33_of_six`: six disjoint connected sets with the nine cross adjacencies give a
  `K_{3,3}` minor (standard branch-set meaning, `MinorModel`).
* `isMinor_of_transport`, `IsMinor.mono`: minor models transport along branch-set maps and
  along subgraph inclusions.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- Some edge of `G` joins `X` and `Y`. -/
def Touch (G : SimpleGraph V) (X Y : Finset V) : Prop := ∃ a ∈ X, ∃ b ∈ Y, G.Adj a b

theorem Touch.symm {G : SimpleGraph V} {X Y : Finset V} (h : Touch G X Y) : Touch G Y X := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨b, hb, a, ha, hab.symm⟩

theorem Touch.mono {G : SimpleGraph V} {X Y X' Y' : Finset V} (h : Touch G X Y) (hX : X ⊆ X')
    (hY : Y ⊆ Y') : Touch G X' Y' := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, hX ha, b, hY hb, hab⟩

variable [DecidableEq V]

/-- The vertex set `S` has no separation of order at most two: whenever `S = A ∪ B` with
`|A ∩ B| ≤ 2` and no edge between `A \ B` and `B \ A`, one side contains the other. -/
def NoSmallSep (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ A B : Finset V, A ∪ B = S → (A ∩ B).card ≤ 2 →
    (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ G.Adj u v) → A ⊆ B ∨ B ⊆ A

omit [DecidableEq V] in
/-- Six disjoint connected sets, three on each side, with all nine cross adjacencies,
form a `K_{3,3}` minor model. -/
theorem isMinor_K33_of_sets {G : SimpleGraph V} (b : Fin 3 ⊕ Fin 3 → Finset V)
    (hc : ∀ w, ConnSet G ↑(b w)) (hd : ∀ w w', w ≠ w' → Disjoint (b w) (b w'))
    (ha : ∀ i j, Touch G (b (Sum.inl i)) (b (Sum.inr j))) : IsMinor K33 G := by
  refine ⟨⟨b, ?_, ?_, hd, ?_⟩⟩
  · intro w
    obtain ⟨x, hx⟩ := (hc w).1
    exact ⟨x, hx⟩
  · intro w
    exact (connSet_iff_induce_connected _ _).1 (hc w)
  · rintro (i | i) (j | j) h
    · simp at h
    · exact ha i j
    · exact (ha j i).symm
    · simp at h

omit [DecidableEq V] in
/-- The six-set form of `isMinor_K33_of_sets`: left sides `X₀ X₁ X₂`, right sides `Y₀ Y₁ Y₂`. -/
theorem isMinor_K33_of_six {G : SimpleGraph V} {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Finset V}
    (cX₀ : ConnSet G ↑X₀) (cX₁ : ConnSet G ↑X₁) (cX₂ : ConnSet G ↑X₂)
    (cY₀ : ConnSet G ↑Y₀) (cY₁ : ConnSet G ↑Y₁) (cY₂ : ConnSet G ↑Y₂)
    (d01 : Disjoint X₀ X₁) (d02 : Disjoint X₀ X₂) (d12 : Disjoint X₁ X₂)
    (e01 : Disjoint Y₀ Y₁) (e02 : Disjoint Y₀ Y₂) (e12 : Disjoint Y₁ Y₂)
    (f00 : Disjoint X₀ Y₀) (f01 : Disjoint X₀ Y₁) (f02 : Disjoint X₀ Y₂)
    (f10 : Disjoint X₁ Y₀) (f11 : Disjoint X₁ Y₁) (f12 : Disjoint X₁ Y₂)
    (f20 : Disjoint X₂ Y₀) (f21 : Disjoint X₂ Y₁) (f22 : Disjoint X₂ Y₂)
    (t00 : Touch G X₀ Y₀) (t01 : Touch G X₀ Y₁) (t02 : Touch G X₀ Y₂)
    (t10 : Touch G X₁ Y₀) (t11 : Touch G X₁ Y₁) (t12 : Touch G X₁ Y₂)
    (t20 : Touch G X₂ Y₀) (t21 : Touch G X₂ Y₁) (t22 : Touch G X₂ Y₂) : IsMinor K33 G := by
  refine isMinor_K33_of_sets (fun w => Sum.elim ![X₀, X₁, X₂] ![Y₀, Y₁, Y₂] w) ?_ ?_ ?_
  · rintro (i | i) <;> fin_cases i <;> assumption
  · rintro (i | i) (j | j) h <;> fin_cases i <;> fin_cases j <;>
      simp_all [Disjoint.symm]
  · intro i j
    fin_cases i <;> fin_cases j <;> assumption

omit [DecidableEq V] in
/-- Minor models are monotone under taking supergraphs of the host. -/
theorem IsMinor.mono {W : Type*} {K : SimpleGraph W} {G G' : SimpleGraph V} (h : IsMinor K G)
    (hle : G ≤ G') : IsMinor K G' := by
  obtain ⟨M⟩ := h
  refine ⟨⟨M.branch, M.branch_nonempty, fun w => ?_, M.branch_disjoint,
    fun w w' hww' => ?_⟩⟩
  · exact (connSet_iff_induce_connected _ _).1 ((M.connSet w).mono hle)
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent w w' hww'
    exact ⟨u, hu, v, hv, hle huv⟩

omit [DecidableEq V] in
/-- Every vertex of a branch set of a minor model of an edge-covered pattern carries an
edge of the host. -/
theorem MinorModel.mem_of_edges {W : Type*} {K : SimpleGraph W} (hK : ∀ w, ∃ w', K.Adj w w')
    {G : SimpleGraph V} (M : MinorModel G K) (T : Set V) (hT : ∀ x y, G.Adj x y → x ∈ T)
    (w : W) {x : V} (hx : x ∈ M.branch w) : x ∈ T := by
  obtain ⟨w', hww'⟩ := hK w
  obtain ⟨u, hu, v, _, huv⟩ := M.branch_adjacent w w' hww'
  have hr := (M.connSet w).2 u hu x hx
  have huT : u ∈ T := hT u v huv
  clear hu hx
  induction hr with
  | refl => exact huT
  | @tail c d _ hcd _ => exact hT d c hcd.1.symm

omit [DecidableEq V] in
/-- **Minor transport.**  If every vertex `x` of the (edge-carrying part `T` of the) graph
`G'` is sent to a connected branch set `φ x` of `G`, distinct vertices to disjoint sets and
edges to adjacent sets, then every minor of `G'` without isolated vertices is a minor of `G`. -/
theorem isMinor_of_transport {W : Type*} {K : SimpleGraph W} (hK : ∀ w, ∃ w', K.Adj w w')
    {G' G : SimpleGraph V} (T : Set V) (hT : ∀ x y, G'.Adj x y → x ∈ T) (φ : V → Finset V)
    (hconn : ∀ x ∈ T, ConnSet G ↑(φ x))
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (φ x) (φ y))
    (hadj : ∀ x y, G'.Adj x y → ∃ a ∈ φ x, ∃ b ∈ φ y, G.Adj a b) (h : IsMinor K G') :
    IsMinor K G := by
  classical
  obtain ⟨M⟩ := h
  have hmem := M.mem_of_edges hK T hT
  refine ⟨⟨fun w => (M.branch w).biUnion φ, ?_, ?_, ?_, ?_⟩⟩
  · intro w
    obtain ⟨x, hx⟩ := M.branch_nonempty w
    obtain ⟨a, ha⟩ := (hconn x (hmem w hx)).1
    exact ⟨a, Finset.mem_biUnion.2 ⟨x, hx, ha⟩⟩
  · intro w
    exact (connSet_iff_induce_connected _ _).1
      (connSet_biUnion T φ hconn hadj _ (M.connSet w) (fun x hx => hmem w hx))
  · intro w w' hww'
    rw [Finset.disjoint_biUnion_left]
    intro x hx
    rw [Finset.disjoint_biUnion_right]
    intro y hy
    have hxy : x ≠ y := by
      rintro rfl
      exact Finset.disjoint_left.1 (M.branch_disjoint w w' hww') hx hy
    exact hdisj x (hmem w hx) y (hmem w' hy) hxy
  · intro w w' hww'
    obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent w w' hww'
    obtain ⟨a, ha, b, hb, hab⟩ := hadj u v huv
    exact ⟨a, Finset.mem_biUnion.2 ⟨u, hu, ha⟩, b, Finset.mem_biUnion.2 ⟨v, hv, hb⟩, hab⟩

omit [DecidableEq V] in
theorem K33_hasNeighbor (w : Fin 3 ⊕ Fin 3) : ∃ w', K33.Adj w w' := by
  rcases w with i | i
  · exact ⟨Sum.inr 0, by simp⟩
  · exact ⟨Sum.inl 0, by simp⟩

omit [DecidableEq V] in
theorem top_five_hasNeighbor (w : Fin 5) : ∃ w', (⊤ : SimpleGraph (Fin 5)).Adj w w' := by
  by_cases h : w = 0
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by simpa using h⟩

/-- Union of two touching connected sets is connected. -/
theorem ConnSet.union_of_touch {G : SimpleGraph V} {X Y : Finset V} (hX : ConnSet G ↑X)
    (hY : ConnSet G ↑Y) (h : Touch G X Y) : ConnSet G ↑(X ∪ Y) := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  have hXs : (↑X : Set V) ⊆ ↑(X ∪ Y) := by intro x hx; simp_all
  have hYs : (↑Y : Set V) ⊆ ↑(X ∪ Y) := by intro x hx; simp_all
  have hab' : RIn G ↑(X ∪ Y) a b := RIn.single hab (hXs ha) (hYs hb)
  refine ⟨⟨a, hXs ha⟩, fun x hx y hy => ?_⟩
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hX.2 x hx y hy).mono_set hXs
  · exact ((hX.2 x hx a ha).mono_set hXs).trans (hab'.trans ((hY.2 b hb y hy).mono_set hYs))
  · exact ((hY.2 x hx b hb).mono_set hYs).trans
      (hab'.symm.trans ((hX.2 a ha y hy).mono_set hXs))
  · exact (hY.2 x hx y hy).mono_set hYs

end LeanPool.K5MinorFreeChoosability
