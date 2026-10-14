/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Hall

/-!
# Decomposition of `K_{3,3}`-minor-free graphs

**Theorem** (`exists_k33Decomp`).  For every finite graph `G` without a `K_{3,3}` minor
(standard branch-set meaning, `K33MinorFree`) there is a spanning supergraph `H ≥ G` with a
`K33Decomp` certificate: `H` is obtained by repeatedly gluing induced pieces along retained
cliques of order at most two (no edges between the private parts), and every leaf piece
`S` is either

* *small*: `|S| ≤ 5`, or
* *prime*: `H[S]` has no `K_5` minor, no `K_{3,3}` minor and no separation of order at
  most two (`NoSmallSep`).

All leaves are moreover `K_{3,3}`-minor-free.  Planarity of the prime leaves would follow
from the reverse direction of Wagner's characterisation (no `K_5`, no `K_{3,3}` minor ⇒
planar), which is **not** proved here; for colourings only `K_5`-minor-freeness of the prime
leaves is needed.

The completion `H` adds exactly the separator edges `xy` of 2-separations `{x, y}`; these are
the virtual edges of 2-sums.  The pieces `H[A] + xy` are minors of the graph being split
(the other side contains an `x`–`y` path through a component of `G - {x, y}`), which is how
`K_{3,3}`-minor-freeness descends.  The `K_5`-minor case of a piece without small separations
is Hall's lemma (`isMinor_K33_of_noSmallSep`).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

variable [DecidableEq V] in
/-- **Wagner-type decomposition certificate** for the vertex set `S` of `H`.  Leaves are
small pieces (`|S| ≤ 5`) or prime pieces (no `K_5` minor, no `K_{3,3}` minor, no separation
of order `≤ 2`); internal nodes glue two pieces `A`, `B` (neither containing the other)
along a retained clique `A ∩ B` of order at most two, with no edges of `H` between `A \ B`
and `B \ A`. -/
inductive K33Decomp (H : SimpleGraph V) : Finset V → Prop
  | small {S : Finset V} : S.card ≤ 5 → K33MinorFree (restrict H ↑S) → K33Decomp H S
  | prime {S : Finset V} : K5MinorFree (restrict H ↑S) → K33MinorFree (restrict H ↑S) →
      NoSmallSep (restrict H ↑S) S → K33Decomp H S
  | glue {A B : Finset V} : ¬ A ⊆ B → ¬ B ⊆ A → (A ∩ B).card ≤ 2 →
      (∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → H.Adj u v) →
      (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) →
      K33Decomp H A → K33Decomp H B → K33Decomp H (A ∪ B)

theorem restrict_congr {H₁ H₂ : SimpleGraph V} {S : Finset V}
    (h : ∀ u ∈ S, ∀ v ∈ S, H₁.Adj u v ↔ H₂.Adj u v) :
    restrict H₁ ↑S = restrict H₂ ↑S := by
  ext u v
  simp only [restrict_adj, Finset.mem_coe]
  constructor
  · rintro ⟨huv, hu, hv⟩; exact ⟨(h u hu v hv).1 huv, hu, hv⟩
  · rintro ⟨huv, hu, hv⟩; exact ⟨(h u hu v hv).2 huv, hu, hv⟩

variable [DecidableEq V] in
/-- A decomposition only depends on the edges inside the decomposed vertex set. -/
theorem K33Decomp.congr {H₁ H₂ : SimpleGraph V} {S : Finset V} (hd : K33Decomp H₁ S)
    (h : ∀ u ∈ S, ∀ v ∈ S, H₁.Adj u v ↔ H₂.Adj u v) : K33Decomp H₂ S := by
  induction hd with
  | small hc hk => exact K33Decomp.small hc (by rwa [← restrict_congr h])
  | prime h5 h33 hs =>
    exact K33Decomp.prime (by rwa [← restrict_congr h]) (by rwa [← restrict_congr h])
      (by rwa [← restrict_congr h])
  | @glue A B hAB hBA hc hcl hnc _ _ ihA ihB =>
    have hA : ∀ u ∈ A, u ∈ A ∪ B := fun u hu => Finset.mem_union_left _ hu
    have hB : ∀ u ∈ B, u ∈ A ∪ B := fun u hu => Finset.mem_union_right _ hu
    refine K33Decomp.glue hAB hBA hc (fun u hu v hv huv => ?_) (fun u hu huB v hv hvA => ?_)
      (ihA fun u hu v hv => h u (hA u hu) v (hA v hv))
      (ihB fun u hu v hv => h u (hB u hu) v (hB v hv))
    · exact (h u (hA u (Finset.mem_inter.1 hu).1) v (hA v (Finset.mem_inter.1 hv).1)).1
        (hcl u hu v hv huv)
    · rw [← h u (hA u hu) v (hB v hv)]
      exact hnc u hu huB v hv hvA

/-- With all edges inside `S`, restriction to `S` changes nothing. -/
theorem restrict_eq_self {H : SimpleGraph V} {S : Finset V} (hS : ∀ u v, H.Adj u v → u ∈ S) :
    restrict H ↑S = H := by
  ext u v
  simp only [restrict_adj, Finset.mem_coe]
  exact ⟨fun h => h.1, fun h => ⟨h, hS u v h, hS v u h.symm⟩⟩

/-- The piece `H[A]` with the clique on `K` added. -/
def pieceGraph (H : SimpleGraph V) (A K : Finset V) : SimpleGraph V where
  Adj u v := u ∈ A ∧ v ∈ A ∧ (H.Adj u v ∨ (u ∈ K ∧ v ∈ K ∧ u ≠ v))
  symm := ⟨fun _ _ ⟨hu, hv, h⟩ => ⟨hv, hu, h.imp (fun h => h.symm)
    (fun ⟨h1, h2, h3⟩ => ⟨h2, h1, Ne.symm h3⟩)⟩⟩
  loopless := ⟨fun _ ⟨_, _, h⟩ => h.elim (fun h => H.irrefl h) (fun h => h.2.2 rfl)⟩

theorem pieceGraph_adj {H : SimpleGraph V} {A K : Finset V} {u v : V} :
    (pieceGraph H A K).Adj u v ↔ u ∈ A ∧ v ∈ A ∧ (H.Adj u v ∨ (u ∈ K ∧ v ∈ K ∧ u ≠ v)) :=
  Iff.rfl

/-- A piece whose separator is already a clique is a subgraph. -/
theorem k33MinorFree_pieceGraph_of_clique {H : SimpleGraph V} {A K : Finset V}
    (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → H.Adj u v) (hH : K33MinorFree H) :
    K33MinorFree (pieceGraph H A K) := by
  intro h
  refine hH (h.mono fun u v huv => ?_)
  obtain ⟨-, -, h | ⟨hu, hv, hne⟩⟩ := huv
  · exact h
  · exact hK u hu v hv hne

variable [DecidableEq V]

/-- A piece `H[A] + xy` is a minor of `H` when a connected set outside `A` touches both
`x` and `y`. -/
theorem k33MinorFree_pieceGraph_of_path {H : SimpleGraph V} {A : Finset V} {x y : V}
    (hxy : x ≠ y) (C : Finset V) (hCA : Disjoint C A) (hC : ConnSet H ↑C)
    (hCx : Touch H C {x}) (hCy : Touch H C {y}) (hH : K33MinorFree H) :
    K33MinorFree (pieceGraph H A {x, y}) := by
  intro h
  let φ : V → Finset V := fun v => if v = x then insert x C else {v}
  have hφx : φ x = insert x C := by simp [φ]
  have hφ : ∀ v, v ≠ x → φ v = {v} := fun v hv => by simp [φ, hv]
  have hmem : ∀ v, v ∈ φ v := fun v => by
    by_cases hv : v = x
    · subst hv; simp [hφx]
    · simp [hφ v hv]
  refine hH (isMinor_of_transport K33_hasNeighbor (↑A)
    (fun u v (huv : (pieceGraph H A {x, y}).Adj u v) => huv.1) φ
    (fun v hv => ?_) (fun v hv w hw hvw => ?_) (fun v w hvw => ?_) h)
  · by_cases hvx : v = x
    · subst hvx
      rw [hφx, Finset.coe_insert]
      obtain ⟨c, hc, x', hx', hcx⟩ := hCx
      rw [Finset.mem_singleton] at hx'
      subst hx'
      exact hC.insert_adj hc hcx.symm
    · rw [hφ v hvx, Finset.coe_singleton]; exact connSet_singleton H v
  · have hvC : ∀ u ∈ (↑A : Set V), u ∉ C := fun u hu huC =>
      Finset.disjoint_left.1 hCA huC (by exact_mod_cast hu)
    by_cases hvx : v = x
    · subst hvx
      have hwx : w ≠ v := Ne.symm hvw
      rw [hφx, hφ w hwx]
      simp [hwx, hvC w hw]
    · by_cases hwx : w = x
      · subst hwx
        rw [hφx, hφ v hvx]
        simp [hvx, hvC v hv]
      · rw [hφ v hvx, hφ w hwx]; simpa using hvw
  · obtain ⟨-, -, hadj | ⟨hv, hw, hne⟩⟩ := hvw
    · exact ⟨v, hmem v, w, hmem w, hadj⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      have hyx : y ≠ x := Ne.symm hxy
      rcases hv with hv | hv <;> rcases hw with hw | hw
      · exact absurd (hv.trans hw.symm) hne
      · obtain ⟨c, hc, y', hy', hcy⟩ := hCy
        rw [Finset.mem_singleton] at hy'
        refine ⟨c, ?_, w, hmem w, ?_⟩
        · rw [hv, hφx]; exact Finset.mem_insert_of_mem hc
        · rw [hw, ← hy']; exact hcy
      · obtain ⟨c, hc, y', hy', hcy⟩ := hCy
        rw [Finset.mem_singleton] at hy'
        refine ⟨v, hmem v, c, ?_, ?_⟩
        · rw [hw, hφx]; exact Finset.mem_insert_of_mem hc
        · rw [hv, ← hy']; exact hcy.symm
      · exact absurd (hv.trans hw.symm) hne

/-- A separation of `S` of order at most two with both private parts nonempty. -/
def IsSmallSep (H : SimpleGraph V) (S A B : Finset V) : Prop :=
  A ∪ B = S ∧ (A ∩ B).card ≤ 2 ∧ (∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v) ∧
    ¬ A ⊆ B ∧ ¬ B ⊆ A

theorem IsSmallSep.symm {H : SimpleGraph V} {S A B : Finset V} (h : IsSmallSep H S A B) :
    IsSmallSep H S B A := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [Finset.union_comm]; exact h1, by rw [Finset.inter_comm]; exact h2,
    fun u hu huA v hv hvB huv => h3 v hv hvB u hu huA huv.symm, h5, h4⟩

/-- In a separation `(A, B)` of minimum order two with separator `{x, y}`, the private part
`B \ A` contains a connected set touching both `x` and `y`. -/
theorem exists_path_of_minSep {H : SimpleGraph V} {S A B : Finset V} {x y : V}
    (hsep : IsSmallSep H S A B) (hK : A ∩ B = {x, y})
    (hmin : ∀ A' B', IsSmallSep H S A' B' → 2 ≤ (A' ∩ B').card) :
    ∃ C : Finset V, C ⊆ B \ A ∧ ConnSet H ↑C ∧ Touch H C {x} ∧ Touch H C {y} := by
  obtain ⟨hcov, -, hnc, hAB, hBA⟩ := hsep
  have hxK : x ∈ A ∩ B := by rw [hK]; simp
  have hyK : y ∈ A ∩ B := by rw [hK]; simp
  obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.1 hBA
  obtain ⟨a, haA, haB⟩ := Finset.not_subset.1 hAB
  have hSA : A ⊆ S := hcov ▸ Finset.subset_union_left
  have hSB : B ⊆ S := hcov ▸ Finset.subset_union_right
  have hbS : b ∈ S \ (A ∩ B) := Finset.mem_sdiff.2 ⟨hSB hbB, fun h => hbA (Finset.mem_inter.1 h).1⟩
  set C := reachIn H (S \ (A ∩ B)) b with hC
  -- `C` stays in `B \ A`
  have hCsub : C ⊆ B \ A := by
    intro w hw
    obtain ⟨-, hbw⟩ := mem_reachIn.1 hw
    have key : ∀ w, RIn H ↑(S \ (A ∩ B)) b w → w ∈ B \ A := by
      intro w hbw
      induction hbw with
      | refl => exact Finset.mem_sdiff.2 ⟨hbB, hbA⟩
      | @tail p q _ hpq ih =>
        obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.1 ih
        have hqS : q ∈ S \ (A ∩ B) := by exact_mod_cast hpq.2.2
        obtain ⟨hqS', hqK⟩ := Finset.mem_sdiff.1 hqS
        by_cases hqB : q ∈ B
        · exact Finset.mem_sdiff.2 ⟨hqB, fun hqA => hqK (Finset.mem_inter.2 ⟨hqA, hqB⟩)⟩
        · have hqA : q ∈ A := by
            rw [← hcov] at hqS'
            exact (Finset.mem_union.1 hqS').resolve_right hqB
          exact absurd hpq.1.symm (hnc q hqA hqB p hpB hpA)
    exact key w hbw
  have hCconn : ConnSet H ↑C := reachIn_conn hbS
  have hbC : b ∈ C := mem_reachIn_self hbS
  -- if `C` misses one end of the separator, the other end alone separates
  have touch : ∀ p q, A ∩ B = {p, q} → Touch H C {p} := by
    intro p q hpq
    by_contra hno
    have hqK : q ∈ A ∩ B := by rw [hpq]; simp
    have hpK : p ∈ A ∩ B := by rw [hpq]; simp
    have hqS : q ∈ S := hSA (Finset.mem_inter.1 hqK).1
    have hqC : q ∉ C := fun h => (Finset.mem_sdiff.1 (hCsub h)).2 (Finset.mem_inter.1 hqK).1
    have hCS : C ⊆ S := fun w hw => hSB (Finset.mem_sdiff.1 (hCsub hw)).1
    have hsep' : IsSmallSep H S (insert q C) (S \ C) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff]
        constructor
        · rintro ((rfl | h) | ⟨h, -⟩)
          · exact hqS
          · exact hCS h
          · exact h
        · intro hw
          by_cases hwC : w ∈ C
          · exact Or.inl (Or.inr hwC)
          · exact Or.inr ⟨hw, hwC⟩
      · refine (Finset.card_le_card (t := {q}) ?_).trans (by simp)
        intro w hw
        obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hw
        rcases Finset.mem_insert.1 h1 with rfl | h
        · simp
        · exact absurd h (Finset.mem_sdiff.1 h2).2
      · intro u hu huB v hv hvA huv
        have huC : u ∈ C := by
          rcases Finset.mem_insert.1 hu with rfl | h
          · exact absurd (Finset.mem_sdiff.2 ⟨hqS, hqC⟩) huB
          · exact h
        obtain ⟨hvS, hvC⟩ := Finset.mem_sdiff.1 hv
        have hvq : v ≠ q := fun h => hvA (h ▸ Finset.mem_insert_self _ _)
        have hvp : v ≠ p := fun h => hno ⟨u, huC, p, Finset.mem_singleton_self _, h ▸ huv⟩
        have hvK : v ∉ A ∩ B := by
          rw [hpq]; simp [hvp, hvq]
        exact hvC (reachIn_closed huC (Finset.mem_sdiff.2 ⟨hvS, hvK⟩) huv)
      · intro h
        exact (Finset.mem_sdiff.1 (h (Finset.mem_insert_of_mem hbC))).2 hbC
      · intro h
        have haS : a ∈ S \ C := Finset.mem_sdiff.2 ⟨hSA haA,
          fun h' => haB (Finset.mem_sdiff.1 (hCsub h')).1⟩
        rcases Finset.mem_insert.1 (h haS) with h' | h'
        · exact haB (h' ▸ (Finset.mem_inter.1 hqK).2)
        · exact (Finset.mem_sdiff.1 haS).2 h'
    have := hmin _ _ hsep'
    have hle : (insert q C ∩ (S \ C)).card ≤ 1 := by
      refine (Finset.card_le_card (t := {q}) ?_).trans (by simp)
      intro w hw
      obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hw
      rcases Finset.mem_insert.1 h1 with rfl | h
      · simp
      · exact absurd h (Finset.mem_sdiff.1 h2).2
    omega
  refine ⟨C, hCsub, hCconn, touch x y hK, touch y x ?_⟩
  rw [hK, Finset.pair_comm]

/-- The recursion behind `exists_k33Decomp`, for graphs whose edges lie in a finite set. -/
theorem exists_k33Decomp_of_support : ∀ (n : ℕ) (H : SimpleGraph V) (S : Finset V),
    S.card = n → (∀ u v, H.Adj u v → u ∈ S) → K33MinorFree H →
    ∃ H' : SimpleGraph V, H ≤ H' ∧ (∀ u v, H'.Adj u v → u ∈ S) ∧ K33Decomp H' S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H S hn hS hK
  by_cases hsmall : S.card ≤ 5
  · exact ⟨H, le_rfl, hS, K33Decomp.small hsmall (by rwa [restrict_eq_self hS])⟩
  by_cases hns : NoSmallSep H S
  · by_cases h5 : K5MinorFree H
    · refine ⟨H, le_rfl, hS, K33Decomp.prime ?_ ?_ ?_⟩ <;> rw [restrict_eq_self hS] <;>
        assumption
    · exfalso
      exact hK (isMinor_K33_of_noSmallSep hS hns (by omega) (not_not.1 h5))
  -- a separation of minimum order
  have hex : ∃ k, ∃ A B, IsSmallSep H S A B ∧ (A ∩ B).card = k := by
    unfold NoSmallSep at hns
    push Not at hns
    obtain ⟨A, B, h1, h2, h3, h4, h5⟩ := hns
    exact ⟨_, A, B, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
  classical
  obtain ⟨A, B, hsep, hk⟩ := Nat.find_spec hex
  have hmin : ∀ A' B', IsSmallSep H S A' B' → (A ∩ B).card ≤ (A' ∩ B').card := by
    intro A' B' h'
    rw [hk]; exact Nat.find_min' hex ⟨A', B', h', rfl⟩
  obtain ⟨hcov, hcard, hnc, hAB, hBA⟩ := hsep
  have hSA : A ⊆ S := hcov ▸ Finset.subset_union_left
  have hSB : B ⊆ S := hcov ▸ Finset.subset_union_right
  set K := A ∩ B with hKdef
  -- both pieces stay `K_{3,3}`-minor-free
  have hpieces : K33MinorFree (pieceGraph H A K) ∧ K33MinorFree (pieceGraph H B K) := by
    by_cases hcl : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → H.Adj u v
    · exact ⟨k33MinorFree_pieceGraph_of_clique hcl hK, k33MinorFree_pieceGraph_of_clique hcl hK⟩
    · push Not at hcl
      obtain ⟨x, hx, y, hy, hxy, hnxy⟩ := hcl
      have hK2 : K = {x, y} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        · rw [Finset.card_pair hxy]; exact hcard
      have hmin2 : ∀ A' B', IsSmallSep H S A' B' → 2 ≤ (A' ∩ B').card := by
        intro A' B' h'
        have := hmin A' B' h'
        rw [hK2, Finset.card_pair hxy] at this
        exact this
      obtain ⟨C, hCsub, hCconn, hCx, hCy⟩ :=
        exists_path_of_minSep ⟨hcov, hcard, hnc, hAB, hBA⟩ hK2 hmin2
      have hK2' : B ∩ A = {x, y} := by rw [Finset.inter_comm]; exact hK2
      obtain ⟨C', hC'sub, hC'conn, hC'x, hC'y⟩ :=
        exists_path_of_minSep (IsSmallSep.symm ⟨hcov, hcard, hnc, hAB, hBA⟩) hK2'
          (fun A' B' h' => hmin2 A' B' h')
      refine ⟨?_, ?_⟩
      · rw [hK2]
        exact k33MinorFree_pieceGraph_of_path hxy C
          (Finset.disjoint_left.2 fun w hw hwA => (Finset.mem_sdiff.1 (hCsub hw)).2 hwA)
          hCconn hCx hCy hK
      · rw [hK2]
        exact k33MinorFree_pieceGraph_of_path hxy C'
          (Finset.disjoint_left.2 fun w hw hwB => (Finset.mem_sdiff.1 (hC'sub hw)).2 hwB)
          hC'conn hC'x hC'y hK
  have hltA : A.card < n := by
    rw [← hn]
    obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.1 hBA
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hSA,
      fun h => hbA (h ▸ hSB hbB)⟩)
  have hltB : B.card < n := by
    rw [← hn]
    obtain ⟨a, haA, haB⟩ := Finset.not_subset.1 hAB
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hSB,
      fun h => haB (h ▸ hSA haA)⟩)
  obtain ⟨HA, hHA, hHAS, hdA⟩ := ih _ hltA (pieceGraph H A K) A rfl
    (fun u v huv => huv.1) hpieces.1
  obtain ⟨HB, hHB, hHBS, hdB⟩ := ih _ hltB (pieceGraph H B K) B rfl
    (fun u v huv => huv.1) hpieces.2
  have hHAS' : ∀ u v, HA.Adj u v → u ∈ A ∧ v ∈ A := fun u v h =>
    ⟨hHAS u v h, hHAS v u h.symm⟩
  have hHBS' : ∀ u v, HB.Adj u v → u ∈ B ∧ v ∈ B := fun u v h =>
    ⟨hHBS u v h, hHBS v u h.symm⟩
  have hKA : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → HA.Adj u v := fun u hu v hv huv =>
    hHA ⟨(Finset.mem_inter.1 hu).1, (Finset.mem_inter.1 hv).1, Or.inr ⟨hu, hv, huv⟩⟩
  have hKB : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → HB.Adj u v := fun u hu v hv huv =>
    hHB ⟨(Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hv).2, Or.inr ⟨hu, hv, huv⟩⟩
  refine ⟨HA ⊔ HB, ?_, ?_, ?_⟩
  · intro u v huv
    have huS := hS u v huv
    have hvS := hS v u huv.symm
    rw [← hcov] at huS hvS
    by_cases huA : u ∈ A
    · by_cases hvA : v ∈ A
      · exact Or.inl (hHA ⟨huA, hvA, Or.inl huv⟩)
      · have hvB := (Finset.mem_union.1 hvS).resolve_left hvA
        by_cases huB : u ∈ B
        · exact Or.inr (hHB ⟨huB, hvB, Or.inl huv⟩)
        · exact absurd huv (hnc u huA huB v hvB hvA)
    · have huB := (Finset.mem_union.1 huS).resolve_left huA
      by_cases hvB : v ∈ B
      · exact Or.inr (hHB ⟨huB, hvB, Or.inl huv⟩)
      · have hvA := (Finset.mem_union.1 hvS).resolve_right hvB
        exact absurd huv.symm (hnc v hvA hvB u huB huA)
  · intro u v huv
    rcases huv with h | h
    · exact hSA (hHAS u v h)
    · exact hSB (hHBS u v h)
  · rw [← hcov]
    refine K33Decomp.glue hAB hBA hcard (fun u hu v hv huv => Or.inl (hKA u hu v hv huv))
      (fun u hu huB v hv hvA huv => ?_) (hdA.congr fun u hu v hv => ?_)
      (hdB.congr fun u hu v hv => ?_)
    · rcases huv with h | h
      · exact hvA (hHAS' u v h).2
      · exact huB (hHBS' u v h).1
    · constructor
      · exact fun h => Or.inl h
      · rintro (h | h)
        · exact h
        · exact hKA u (Finset.mem_inter.2 ⟨hu, (hHBS' u v h).1⟩) v
            (Finset.mem_inter.2 ⟨hv, (hHBS' u v h).2⟩) h.ne
    · constructor
      · exact fun h => Or.inr h
      · rintro (h | h)
        · exact hKB u (Finset.mem_inter.2 ⟨(hHAS' u v h).1, hu⟩) v
            (Finset.mem_inter.2 ⟨(hHAS' u v h).2, hv⟩) h.ne
        · exact h

/-- **Structure of `K_{3,3}`-minor-free graphs** (existence part of Wagner's theorem, with
prime pieces certified `K_5`- and `K_{3,3}`-minor-free and without separations of order at
most two; see the module docstring).  Every finite graph `G` without a `K_{3,3}` minor is a
spanning subgraph of a graph `H` with a `K33Decomp` certificate on all vertices. -/
theorem exists_k33Decomp [Fintype V] (G : SimpleGraph V) (hG : K33MinorFree G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ K33Decomp H Finset.univ := by
  obtain ⟨H, hGH, -, hd⟩ :=
    exists_k33Decomp_of_support _ G Finset.univ rfl (fun _ _ _ => Finset.mem_univ _) hG
  exact ⟨H, hGH, hd⟩

end LeanPool.K5MinorFreeChoosability
