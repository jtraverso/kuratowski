/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Contract

/-!
# Contractible edges

**Lemma** (Tutte; Thomassen; Diestel, Lemma 3.2.1).  If the vertex set `S` of `G` (with all edges
inside `S`) has no separation of order at most two and at least two vertices, then some edge
`xy` can be contracted without creating a separation of order at most two:
`exists_contractible_edge_of_noSmallSep`.

The proof is the classical minimal-side argument.  If no edge is contractible, every edge `xy`
lies in a separator `{x, y, w}` (`exists_tripleSep_of_not_noSmallSep`).  Choose such a
separator with a side `P` of minimum size; `w` has a neighbour `v ∈ P`, and the separator
`{w, v, u}` of the edge `wv` has a component `D ⊊ P` avoiding `x, y`, a contradiction.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- `R` is one side of a separation of `S` with separator `Z`: a nonempty part of `S` disjoint
from `Z`, with something left outside `R ∪ Z`, and no edge from `R` to `S \ (R ∪ Z)`. -/
def IsSide (G : SimpleGraph V) (S Z R : Finset V) : Prop :=
  R ⊆ S ∧ Disjoint R Z ∧ R.Nonempty ∧ (S \ (R ∪ Z)).Nonempty ∧
    ∀ p ∈ R, ∀ q ∈ S, q ∉ R → q ∉ Z → ¬ G.Adj p q

theorem IsSide.compl {S Z R : Finset V} (h : IsSide G S Z R) :
    IsSide G S Z (S \ (R ∪ Z)) := by
  obtain ⟨hRS, hRZ, hRne, hcne, hcr⟩ := h
  refine ⟨Finset.sdiff_subset, ?_, hcne, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha haZ
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at ha
    exact ha.2.2 haZ
  · obtain ⟨r, hr⟩ := hRne
    refine ⟨r, Finset.mem_sdiff.2 ⟨hRS hr, ?_⟩⟩
    intro h
    rcases Finset.mem_union.1 h with h | h
    · exact (Finset.mem_sdiff.1 h).2 (Finset.mem_union_left _ hr)
    · exact Finset.disjoint_left.1 hRZ hr h
  · intro p hp q hq hqc hqZ hpq
    obtain ⟨hpS, hpRZ⟩ := Finset.mem_sdiff.1 hp
    have hpR : p ∉ R := fun h => hpRZ (Finset.mem_union_left _ h)
    have hpZ : p ∉ Z := fun h => hpRZ (Finset.mem_union_right _ h)
    have hqR : q ∈ R := by
      by_contra hqR
      exact hqc (Finset.mem_sdiff.2 ⟨hq, fun h => (Finset.mem_union.1 h).elim hqR hqZ⟩)
    exact hcr q hqR p hpS hpR hpZ hpq.symm

/-- A side with a separator of at most two vertices contradicts `NoSmallSep`. -/
theorem IsSide.false {S Z R : Finset V} (h : IsSide G S Z R) (hsep : NoSmallSep G S)
    (hZS : Z ⊆ S) (hZ : Z.card ≤ 2) : False := by
  obtain ⟨hRS, hRZ, ⟨r, hr⟩, ⟨q, hq⟩, hcr⟩ := h
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hq
  have hcov : (R ∪ Z) ∪ (S \ R) = S := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | ⟨h, -⟩)
      · exact hRS h
      · exact hZS h
      · exact h
    · intro ha
      by_cases haR : a ∈ R
      · exact Or.inl (Or.inl haR)
      · exact Or.inr ⟨ha, haR⟩
  have hint : (R ∪ Z) ∩ (S \ R) ⊆ Z := by
    intro a ha
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at ha
    rcases ha.1 with h | h
    · exact absurd h ha.2.2
    · exact h
  rcases hsep (R ∪ Z) (S \ R) hcov ((Finset.card_le_card hint).trans hZ) (by
      intro u hu huB v hv hvA huv
      simp only [Finset.mem_union, Finset.mem_sdiff, not_and, not_not, not_or] at hu huB hv hvA
      have huR : u ∈ R := by
        rcases hu with h | h
        · exact h
        · exact huB (hZS h)
      exact hcr u huR v hv.1 hv.2 hvA.2 huv) with h | h
  · have := h (Finset.mem_union_left _ hr)
    exact (Finset.mem_sdiff.1 this).2 hr
  · have := h (Finset.mem_sdiff.2 ⟨hq.1, hq.2.1⟩)
    rcases Finset.mem_union.1 this with h' | h'
    · exact hq.2.1 h'
    · exact hq.2.2 h'

/-- An edge `xy` lying in a separator `{x, y, w}` with side `P`. -/
def TripleSep (G : SimpleGraph V) (S : Finset V) (x y w : V) (P : Finset V) : Prop :=
  G.Adj x y ∧ w ≠ x ∧ w ≠ y ∧ x ∈ S ∧ y ∈ S ∧ w ∈ S ∧ IsSide G S {x, y, w} P

/-- If `x ∈ A \ B` for a small separation `(A, B)` of the contraction, then `G` has a small
separation. -/
theorem false_of_contract_sep_of_mem {S A B : Finset V} {x y : V}
    (hsep : NoSmallSep G S) (hxy : G.Adj x y)
    (hcov : A ∪ B = S.erase y) (hcard : (A ∩ B).card ≤ 2)
    (hcross : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ (contractGraph G x y).Adj u v)
    (hBA : ¬ B ⊆ A) (hxA : x ∈ A) (hxB : x ∉ B) : False := by
  have hAS : ∀ a ∈ A, a ∈ S ∧ a ≠ y := fun a ha => by
    have : a ∈ S.erase y := hcov ▸ Finset.mem_union_left _ ha
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hBS : ∀ b ∈ B, b ∈ S ∧ b ≠ y := fun b hb => by
    have : b ∈ S.erase y := hcov ▸ Finset.mem_union_right _ hb
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hside : IsSide G S (A ∩ B) (B \ A) := by
    refine ⟨fun b hb => (hBS b (Finset.mem_sdiff.1 hb).1).1, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro a ha ha'
      exact (Finset.mem_sdiff.1 ha).2 (Finset.mem_inter.1 ha').1
    · obtain ⟨b, hb, hbA⟩ := Finset.not_subset.1 hBA
      exact ⟨b, Finset.mem_sdiff.2 ⟨hb, hbA⟩⟩
    · refine ⟨x, Finset.mem_sdiff.2 ⟨(hAS x hxA).1, ?_⟩⟩
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact (Finset.mem_sdiff.1 h).2 hxA
      · exact hxB (Finset.mem_inter.1 h).2
    · intro p hp q hq hqR hqZ hpq
      obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.1 hp
      have hpy : p ≠ y := (hBS p hpB).2
      have hpx : p ≠ x := fun h => hpA (h ▸ hxA)
      by_cases hqy : q = y
      · subst hqy
        exact hcross x hxA hxB p hpB hpA
          ((contractGraph_adj_x hxy.ne).2 ⟨hpx, hpy, Or.inr hpq.symm⟩)
      · have hq' : q ∈ A ∪ B := hcov ▸ Finset.mem_erase.2 ⟨hqy, hq⟩
        have hqA : q ∈ A := by
          rcases Finset.mem_union.1 hq' with h | h
          · exact h
          · exact absurd (Finset.mem_sdiff.2 ⟨h, fun h' => hqZ (Finset.mem_inter.2 ⟨h', h⟩)⟩)
              hqR
        have hqB : q ∉ B := fun h => hqZ (Finset.mem_inter.2 ⟨hqA, h⟩)
        by_cases hqx : q = x
        · subst hqx
          exact hcross q hqA hqB p hpB hpA
            ((contractGraph_adj_x hxy.ne).2 ⟨hpx, hpy, Or.inl hpq.symm⟩)
        · exact hcross q hqA hqB p hpB hpA
            ((contractGraph_adj_of_ne hqx hpx hqy hpy).2 hpq.symm)
  refine hside.false hsep ?_ hcard
  intro a ha
  exact (hAS a (Finset.mem_inter.1 ha).1).1

/-- A non-contractible edge lies in a separator of order three. -/
theorem exists_tripleSep_of_not_noSmallSep {S : Finset V} {x y : V}
    (hS : ∀ u v, G.Adj u v → u ∈ S) (hsep : NoSmallSep G S) (hxy : G.Adj x y)
    (hn : ¬ NoSmallSep (contractGraph G x y) (S.erase y)) :
    ∃ w P, TripleSep G S x y w P := by
  unfold NoSmallSep at hn
  push Not at hn
  obtain ⟨A, B, hcov, hcard, hcross, hAB, hBA⟩ := hn
  have hxS : x ∈ S.erase y := Finset.mem_erase.2 ⟨hxy.ne, hS x y hxy⟩
  rw [← hcov] at hxS
  have hAS : ∀ a ∈ A, a ∈ S ∧ a ≠ y := fun a ha => by
    have : a ∈ S.erase y := hcov ▸ Finset.mem_union_left _ ha
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hBS : ∀ b ∈ B, b ∈ S ∧ b ≠ y := fun b hb => by
    have : b ∈ S.erase y := hcov ▸ Finset.mem_union_right _ hb
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  by_cases hxB : x ∈ B
  · by_cases hxA : x ∈ A
    · -- `x` lies in the separator of the contraction
      have hxI : x ∈ A ∩ B := Finset.mem_inter.2 ⟨hxA, hxB⟩
      by_cases hc1 : (A ∩ B).card ≤ 1
      · exfalso
        have hside : IsSide G S (insert y (A ∩ B)) (B \ A) := by
          refine ⟨fun b hb => (hBS b (Finset.mem_sdiff.1 hb).1).1, ?_, ?_, ?_, ?_⟩
          · rw [Finset.disjoint_left]
            intro a ha ha'
            rcases Finset.mem_insert.1 ha' with h | h
            · exact (hBS a (Finset.mem_sdiff.1 ha).1).2 h
            · exact (Finset.mem_sdiff.1 ha).2 (Finset.mem_inter.1 h).1
          · obtain ⟨b, hb, hbA⟩ := Finset.not_subset.1 hBA
            exact ⟨b, Finset.mem_sdiff.2 ⟨hb, hbA⟩⟩
          · obtain ⟨a, ha, haB⟩ := Finset.not_subset.1 hAB
            refine ⟨a, Finset.mem_sdiff.2 ⟨(hAS a ha).1, ?_⟩⟩
            intro h
            rcases Finset.mem_union.1 h with h | h
            · exact (Finset.mem_sdiff.1 h).2 ha
            · rcases Finset.mem_insert.1 h with h | h
              · exact (hAS a ha).2 h
              · exact haB (Finset.mem_inter.1 h).2
          · intro p hp q hq hqR hqZ hpq
            obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.1 hp
            have hqy : q ≠ y := fun h => hqZ (Finset.mem_insert.2 (Or.inl h))
            have hq' : q ∈ A ∪ B := hcov ▸ Finset.mem_erase.2 ⟨hqy, hq⟩
            have hqI : q ∉ A ∩ B := fun h => hqZ (Finset.mem_insert_of_mem h)
            have hqA : q ∈ A := by
              rcases Finset.mem_union.1 hq' with h | h
              · exact h
              · exact absurd (Finset.mem_sdiff.2 ⟨h, fun h' => hqI (Finset.mem_inter.2 ⟨h', h⟩)⟩)
                  hqR
            have hqB : q ∉ B := fun h => hqI (Finset.mem_inter.2 ⟨hqA, h⟩)
            have hqx : q ≠ x := fun h => hqB (h ▸ hxB)
            have hpx : p ≠ x := fun h => hpA (h ▸ hxA)
            exact hcross q hqA hqB p hpB hpA
              ((contractGraph_adj_of_ne hqx hpx hqy (hBS p hpB).2).2 hpq.symm)
        refine hside.false hsep ?_ ?_
        · intro a ha
          rcases Finset.mem_insert.1 ha with h | h
          · exact h ▸ hS y x hxy.symm
          · exact (hAS a (Finset.mem_inter.1 h).1).1
        · exact (Finset.card_insert_le _ _).trans (by omega)
      · have hc2 : (A ∩ B).card = 2 := by omega
        obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.1 hc2
        obtain ⟨w, hw, hwx⟩ : ∃ w, A ∩ B = {x, w} ∧ w ≠ x := by
          rw [he] at hxI
          rcases Finset.mem_insert.1 hxI with h | h
          · exact ⟨b, by rw [he, h], fun e => hab (h.symm.trans e.symm)⟩
          · rw [Finset.mem_singleton] at h
            exact ⟨a, by rw [he, h, Finset.pair_comm], fun e => hab (e.trans h)⟩
        have hwI : w ∈ A ∩ B := by rw [hw]; simp
        have hwB := (Finset.mem_inter.1 hwI).2
        have hwA := (Finset.mem_inter.1 hwI).1
        refine ⟨w, B \ A, hxy, hwx, (hBS w hwB).2, (hAS x hxA).1, hS y x hxy.symm,
          (hBS w hwB).1, fun b hb => (hBS b (Finset.mem_sdiff.1 hb).1).1, ?_, ?_, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro c hc hc'
          obtain ⟨hcB, hcA⟩ := Finset.mem_sdiff.1 hc
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
          rcases hc' with h | h | h
          · exact hcA (h ▸ hxA)
          · exact (hBS c hcB).2 h
          · exact hcA (h ▸ hwA)
        · obtain ⟨b, hb, hbA⟩ := Finset.not_subset.1 hBA
          exact ⟨b, Finset.mem_sdiff.2 ⟨hb, hbA⟩⟩
        · obtain ⟨c, hc, hcB⟩ := Finset.not_subset.1 hAB
          refine ⟨c, ?_⟩
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, not_or, not_and]
          exact ⟨(hAS c hc).1, fun h => absurd h hcB, fun h => hcB (h ▸ hxB), (hAS c hc).2,
            fun h => hcB (h ▸ hwB)⟩
        · intro p hp q hq hqR hqZ hpq
          obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.1 hp
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqZ
          obtain ⟨hqx, hqy, hqw⟩ := hqZ
          have hq' : q ∈ A ∪ B := hcov ▸ Finset.mem_erase.2 ⟨hqy, hq⟩
          have hqI : q ∉ A ∩ B := by rw [hw]; simp [hqx, hqw]
          have hqA : q ∈ A := by
            rcases Finset.mem_union.1 hq' with h | h
            · exact h
            · exact absurd (Finset.mem_sdiff.2 ⟨h, fun h' => hqI (Finset.mem_inter.2 ⟨h', h⟩)⟩)
                hqR
          have hqB : q ∉ B := fun h => hqI (Finset.mem_inter.2 ⟨hqA, h⟩)
          have hpx : p ≠ x := fun h => hpA (h ▸ hxA)
          exact hcross q hqA hqB p hpB hpA
            ((contractGraph_adj_of_ne hqx hpx hqy (hBS p hpB).2).2 hpq.symm)
    · exfalso
      have hcov' : B ∪ A = S.erase y := by rw [Finset.union_comm]; exact hcov
      have hcard' : (B ∩ A).card ≤ 2 := by rw [Finset.inter_comm]; exact hcard
      exact false_of_contract_sep_of_mem hsep hxy hcov' hcard'
        (fun u hu huA v hv hvB huv => hcross v hv hvB u hu huA huv.symm) hAB hxB hxA
  · exfalso
    have hxA : x ∈ A := (Finset.mem_union.1 hxS).resolve_right hxB
    exact false_of_contract_sep_of_mem hsep hxy hcov hcard hcross hBA hxA hxB

/-- A vertex set without small separations and with at least two vertices carries an edge. -/
theorem exists_adj_of_noSmallSep {S : Finset V} (hsep : NoSmallSep G S) (h2 : 2 ≤ S.card)
    {v : V} (hv : v ∈ S) : ∃ u, G.Adj v u := by
  by_contra hn
  push Not at hn
  have hside : IsSide G S ∅ {v} := by
    refine ⟨Finset.singleton_subset_iff.2 hv, Finset.disjoint_empty_right _,
      Finset.singleton_nonempty v, ?_, ?_⟩
    · obtain ⟨a, ha, hav⟩ := Finset.exists_mem_ne h2 v
      exact ⟨a, by simp [ha, hav]⟩
    · intro p hp q _ _ _ hpq
      rw [Finset.mem_singleton] at hp
      exact hn q (hp ▸ hpq)
  exact hside.false hsep (Finset.empty_subset _) (by simp)

/-- **Contractible edges.**  A vertex set `S` (containing all edges of `G`) with at least two
vertices and without separations of order at most two has an edge `xy` whose contraction has
no separation of order at most two on `S \ {y}`. -/
theorem exists_contractible_edge_of_noSmallSep {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hsep : NoSmallSep G S) (h2 : 2 ≤ S.card) :
    ∃ x y, G.Adj x y ∧ NoSmallSep (contractGraph G x y) (S.erase y) := by
  classical
  by_contra hall
  push Not at hall
  have hex : ∃ n, ∃ x y w P, TripleSep G S x y w P ∧ P.card = n := by
    obtain ⟨v, hv⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
    obtain ⟨u, hvu⟩ := exists_adj_of_noSmallSep hsep h2 hv
    obtain ⟨w, P, hT⟩ := exists_tripleSep_of_not_noSmallSep hS hsep hvu (hall v u hvu)
    exact ⟨_, v, u, w, P, hT, rfl⟩
  obtain ⟨x, y, w, P, hT, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ x' y' w' P', TripleSep G S x' y' w' P' → Nat.find hex ≤ P'.card :=
    fun x' y' w' P' h => Nat.find_min' hex ⟨x', y', w', P', h, rfl⟩
  obtain ⟨hxy, hwx, hwy, hxS, hyS, hwS, hPS, hPZ, hPne, hPc, hPcr⟩ := hT
  have hxP : x ∉ P := fun h => Finset.disjoint_left.1 hPZ h (by simp)
  have hyP : y ∉ P := fun h => Finset.disjoint_left.1 hPZ h (by simp)
  have hwP : w ∉ P := fun h => Finset.disjoint_left.1 hPZ h (by simp)
  -- (i) `w` has a neighbour in `P`
  obtain ⟨v, hvP, hwv⟩ : ∃ v ∈ P, G.Adj w v := by
    by_contra hnv
    push Not at hnv
    have hside : IsSide G S {x, y} P := by
      refine ⟨hPS, ?_, hPne, ⟨w, ?_⟩, ?_⟩
      · rw [Finset.disjoint_left]
        intro a ha ha'
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with rfl | rfl
        · exact hxP ha
        · exact hyP ha
      · simp [hwS, hwP, hwx, hwy]
      · intro p hp q hq hqP hqZ hpq
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqZ
        by_cases hqw : q = w
        · exact hnv p hp (hqw ▸ hpq.symm)
        · exact hPcr p hp q hq hqP (by simp [hqZ.1, hqZ.2, hqw]) hpq
    refine hside.false hsep ?_ (Finset.card_le_two)
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hxS
    · exact hyS
  have hvS : v ∈ S := hPS hvP
  have hvx : v ≠ x := fun h => hxP (h ▸ hvP)
  have hvy : v ≠ y := fun h => hyP (h ▸ hvP)
  -- (ii) the edge `wv` lies in a separator `{w, v, u}`
  obtain ⟨u, P₂, hT₂⟩ := exists_tripleSep_of_not_noSmallSep hS hsep hwv (hall w v hwv)
  obtain ⟨-, huw, huv, -, -, huS, hside₂⟩ := hT₂
  -- (iii) a side of `{w, v, u}` avoiding `x` and `y`
  obtain ⟨R, hR, hxR, hyR⟩ : ∃ R, IsSide G S {w, v, u} R ∧ x ∉ R ∧ y ∉ R := by
    by_cases hP₂ : x ∈ P₂ ∨ y ∈ P₂
    · refine ⟨_, hside₂.compl, ?_, ?_⟩
      · intro hxR
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hxR
        rcases hP₂ with h | h
        · exact hxR.2.1 h
        · exact hside₂.2.2.2.2 y h x hxS hxR.2.1 hxR.2.2 hxy.symm
      · intro hyR
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hyR
        rcases hP₂ with h | h
        · exact hside₂.2.2.2.2 x h y hyS hyR.2.1 hyR.2.2 hxy
        · exact hyR.2.1 h
    · push Not at hP₂
      exact ⟨P₂, hside₂, hP₂.1, hP₂.2⟩
  obtain ⟨hRS, hRZ, ⟨t, ht⟩, -, hRcr⟩ := hR
  -- (iv) the component `D` of `t` in `R`
  set D := reachIn G R t with hD
  have hDR : D ⊆ R := reachIn_sub R t
  have hDZ : ∀ d ∈ D, d ≠ w ∧ d ≠ v ∧ d ≠ u := by
    intro d hd
    have := Finset.disjoint_left.1 hRZ (hDR hd)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
    exact this
  have hDcr : ∀ p ∈ D, ∀ q ∈ S, q ∉ D → q ≠ w → q ≠ v → q ≠ u → ¬ G.Adj p q := by
    intro p hp q hq hqD hqw hqv hqu hpq
    by_cases hqR : q ∈ R
    · exact hqD (reachIn_closed hp hqR hpq)
    · exact hRcr p (hDR hp) q hq hqR (by simp [hqw, hqv, hqu]) hpq
  -- (v) `v` has a neighbour in `D`
  obtain ⟨t', ht'D, hvt'⟩ : ∃ t' ∈ D, G.Adj v t' := by
    by_contra hnv
    push Not at hnv
    have hside : IsSide G S {w, u} D := by
      refine ⟨hDR.trans hRS, ?_, ⟨t, mem_reachIn_self ht⟩, ⟨v, ?_⟩, ?_⟩
      · rw [Finset.disjoint_left]
        intro a ha ha'
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with rfl | rfl
        · exact (hDZ a ha).1 rfl
        · exact (hDZ a ha).2.2 rfl
      · simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or]
        exact ⟨hvS, fun h => (hDZ v h).2.1 rfl, hwv.ne.symm, Ne.symm huv⟩
      · intro p hp q hq hqD hqZ hpq
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqZ
        by_cases hqv : q = v
        · exact hnv p hp (hqv ▸ hpq.symm)
        · exact hDcr p hp q hq hqD hqZ.1 hqv hqZ.2 hpq
    refine hside.false hsep ?_ (Finset.card_le_two)
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hwS
    · exact huS
  -- (vi)-(vii) `D ⊆ P`
  have hDok : ∀ d ∈ D, d ∈ S ∧ d ≠ x ∧ d ≠ y ∧ d ≠ w := fun d hd =>
    ⟨hRS (hDR hd), fun h => hxR (h ▸ hDR hd), fun h => hyR (h ▸ hDR hd), (hDZ d hd).1⟩
  have step : ∀ a b, a ∈ P → b ∈ D → G.Adj a b → b ∈ P := by
    intro a b ha hb hab
    by_contra hbP
    obtain ⟨hbS, hbx, hby, hbw⟩ := hDok b hb
    exact hPcr a ha b hbS hbP (by simp [hbx, hby, hbw]) hab
  have ht'P : t' ∈ P := step v t' hvP ht'D hvt'
  have hDP : D ⊆ P := by
    intro d hd
    have hr := (reachIn_conn (G := G) ht).2 t' ht'D d hd
    induction hr with
    | refl => exact ht'P
    | @tail b c _ hbc ih =>
      exact step b c (ih (by exact_mod_cast hbc.2.1)) (by exact_mod_cast hbc.2.2) hbc.1
  have hvD : v ∉ D := fun h => (hDZ v h).2.1 rfl
  have hlt : D.card < P.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hDP, fun h => hvD (h ▸ hvP)⟩)
  -- (viii) the new triple separation contradicts minimality
  have hT' : TripleSep G S w v u D := by
    refine ⟨hwv, huw, huv, hwS, hvS, huS, hDR.trans hRS, ?_, ⟨t, mem_reachIn_self ht⟩, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro a ha ha'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
      obtain ⟨h1, h2, h3⟩ := hDZ a ha
      rcases ha' with h | h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
    · by_cases hxu : x = u
      · refine ⟨y, ?_⟩
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or]
        exact ⟨hyS, fun h => hyR (hDR h), Ne.symm hwy, Ne.symm hvy,
          fun h => hxy.ne (hxu.trans h.symm)⟩
      · refine ⟨x, ?_⟩
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or]
        exact ⟨hxS, fun h => hxR (hDR h), Ne.symm hwx, Ne.symm hvx, hxu⟩
    · intro p hp q hq hqD hqZ hpq
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqZ
      exact hDcr p hp q hq hqD hqZ.1 hqZ.2.1 hqZ.2.2 hpq
  have := hmin w v u D hT'
  omega

end LeanPool.K5MinorFreeChoosability
