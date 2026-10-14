/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Kuratowski
public import LeanPool.K5MinorFreeChoosability.Wagner.Glue
public import LeanPool.K5MinorFreeChoosability.Wagner.Decomposition

/-!
# Wagner's theorem, reverse direction

`isPlanar_of_k5MinorFree_of_k33MinorFree`: every finite graph with neither a `K_5` minor nor a
`K_{3,3}` minor (standard branch-set meaning) is planar in the rotation-system model `IsPlanar`.

Proof: strong induction on the size of a finite vertex set `S` carrying all edges.

* If `S` has no separation of order at most two (`NoSmallSep`), this is Kuratowski's theorem
  for prime pieces, `isPlanar_of_noSmallSep`.
* Otherwise pick a separation `(A, B)` of minimum order `k ≤ 2` with separator `K = A ∩ B` and
  pass to the pieces `H[A] + clique(K)` and `H[B] + clique(K)` (`pieceGraph`).  The pieces are
  again `K_5`- and `K_{3,3}`-minor-free: if `K` is already a clique they are subgraphs, and if
  `K = {x, y}` is a non-edge then minimality yields an `x`–`y` path through the other side, so the
  piece is a minor (`isMinor_of_isMinor_pieceGraph_of_path`).  Both pieces are planar by
  induction; their union is planar by the rotation-system gluing theorems
  `isPlanar_sup_of_le_one` (order `0` or `1`, including disconnected graphs) and
  `isPlanar_sup_of_two` (order `2`, along the common edge `xy`); `H` is a subgraph of the union.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- A subgraph of a planar graph is planar. -/
theorem IsPlanar.mono [Finite V] {G G' : SimpleGraph V} (hG : IsPlanar G') (hle : G ≤ G') :
    IsPlanar G :=
  hG.of_isMinor (IsMinor.mono ⟨MinorModel.ofIso SimpleGraph.Iso.refl⟩ hle)

/-- `K_5`-minor-freeness descends to a piece whose separator is already a clique. -/
theorem k5MinorFree_pieceGraph_of_clique {H : SimpleGraph V} {A K : Finset V}
    (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → H.Adj u v) (hH : K5MinorFree H) :
    K5MinorFree (pieceGraph H A K) := by
  unfold K5MinorFree at hH ⊢
  rw [cliqueMinorFree_iff_not_isMinor] at hH ⊢
  refine fun h => hH (h.mono fun u v huv => ?_)
  obtain ⟨-, -, h | ⟨hu, hv, hne⟩⟩ := huv
  · exact h
  · exact hK u hu v hv hne

variable [DecidableEq V]

/-- A piece `H[A] + xy` is a minor of `H` when a connected set outside `A` touches both `x`
and `y`; hence every pattern without isolated vertices that is a minor of the piece is a minor
of `H`. -/
theorem isMinor_of_isMinor_pieceGraph_of_path {W : Type*} {K : SimpleGraph W}
    (hK : ∀ w, ∃ w', K.Adj w w') {H : SimpleGraph V} {A : Finset V} {x y : V}
    (hxy : x ≠ y) (C : Finset V) (hCA : Disjoint C A) (hC : ConnSet H ↑C)
    (hCx : Touch H C {x}) (hCy : Touch H C {y}) (h : IsMinor K (pieceGraph H A {x, y})) :
    IsMinor K H := by
  let φ : V → Finset V := fun v => if v = x then insert x C else {v}
  have hφx : φ x = insert x C := by simp [φ]
  have hφ : ∀ v, v ≠ x → φ v = {v} := fun v hv => by simp [φ, hv]
  have hmem : ∀ v, v ∈ φ v := fun v => by
    by_cases hv : v = x
    · subst hv; simp [hφx]
    · simp [hφ v hv]
  refine isMinor_of_transport hK (↑A)
    (fun u v (huv : (pieceGraph H A {x, y}).Adj u v) => huv.1) φ
    (fun v hv => ?_) (fun v hv w hw hvw => ?_) (fun v w hvw => ?_) h
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

/-- `K_5`-minor-freeness descends to a piece `H[A] + xy` when the other side connects `x`
and `y`. -/
theorem k5MinorFree_pieceGraph_of_path {H : SimpleGraph V} {A : Finset V} {x y : V}
    (hxy : x ≠ y) (C : Finset V) (hCA : Disjoint C A) (hC : ConnSet H ↑C)
    (hCx : Touch H C {x}) (hCy : Touch H C {y}) (hH : K5MinorFree H) :
    K5MinorFree (pieceGraph H A {x, y}) := by
  unfold K5MinorFree at hH ⊢
  rw [cliqueMinorFree_iff_not_isMinor] at hH ⊢
  exact fun h => hH (isMinor_of_isMinor_pieceGraph_of_path top_five_hasNeighbor hxy C hCA hC
    hCx hCy h)

variable [Finite V]

omit [DecidableEq V] in
/-- The induction behind `isPlanar_of_k5MinorFree_of_k33MinorFree`, for graphs whose edges lie
in a finite vertex set `S`. -/
theorem isPlanar_of_minorFree_aux : ∀ (n : ℕ) (H : SimpleGraph V) (S : Finset V),
    S.card = n → (∀ u v, H.Adj u v → u ∈ S) → K5MinorFree H → K33MinorFree H →
    IsPlanar H := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H S hn hS h5 hK
  by_cases hns : NoSmallSep H S
  · exact isPlanar_of_noSmallSep hS hns h5 hK
  -- a separation of minimum order
  have hex : ∃ k, ∃ A B, IsSmallSep H S A B ∧ (A ∩ B).card = k := by
    unfold NoSmallSep at hns
    push Not at hns
    obtain ⟨A, B, h1, h2, h3, h4, h5⟩ := hns
    exact ⟨_, A, B, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
  obtain ⟨A, B, hsep, hk⟩ := Nat.find_spec hex
  have hmin : ∀ A' B', IsSmallSep H S A' B' → (A ∩ B).card ≤ (A' ∩ B').card := by
    intro A' B' h'
    rw [hk]; exact Nat.find_min' hex ⟨A', B', h', rfl⟩
  obtain ⟨hcov, hcard, hnc, hAB, hBA⟩ := hsep
  have hSA : A ⊆ S := hcov ▸ Finset.subset_union_left
  have hSB : B ⊆ S := hcov ▸ Finset.subset_union_right
  set K := A ∩ B with hKdef
  -- both pieces stay `K_5`- and `K_{3,3}`-minor-free
  have hpieces : (K5MinorFree (pieceGraph H A K) ∧ K33MinorFree (pieceGraph H A K)) ∧
      (K5MinorFree (pieceGraph H B K) ∧ K33MinorFree (pieceGraph H B K)) := by
    by_cases hcl : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → H.Adj u v
    · exact ⟨⟨k5MinorFree_pieceGraph_of_clique hcl h5, k33MinorFree_pieceGraph_of_clique hcl hK⟩,
        ⟨k5MinorFree_pieceGraph_of_clique hcl h5, k33MinorFree_pieceGraph_of_clique hcl hK⟩⟩
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
      have hdA : Disjoint C A :=
        Finset.disjoint_left.2 fun w hw hwA => (Finset.mem_sdiff.1 (hCsub hw)).2 hwA
      have hdB : Disjoint C' B :=
        Finset.disjoint_left.2 fun w hw hwB => (Finset.mem_sdiff.1 (hC'sub hw)).2 hwB
      rw [hK2]
      exact ⟨⟨k5MinorFree_pieceGraph_of_path hxy C hdA hCconn hCx hCy h5,
          k33MinorFree_pieceGraph_of_path hxy C hdA hCconn hCx hCy hK⟩,
        ⟨k5MinorFree_pieceGraph_of_path hxy C' hdB hC'conn hC'x hC'y h5,
          k33MinorFree_pieceGraph_of_path hxy C' hdB hC'conn hC'x hC'y hK⟩⟩
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
  have hsA : ∀ u v, (pieceGraph H A K).Adj u v → u ∈ A := fun u v huv => huv.1
  have hsB : ∀ u v, (pieceGraph H B K).Adj u v → u ∈ B := fun u v huv => huv.1
  obtain ⟨MA⟩ := ih _ hltA (pieceGraph H A K) A rfl hsA hpieces.1.1 hpieces.1.2
  obtain ⟨MB⟩ := ih _ hltB (pieceGraph H B K) B rfl hsB hpieces.2.1 hpieces.2.2
  -- `H` is a subgraph of the union of the pieces
  have hle : H ≤ pieceGraph H A K ⊔ pieceGraph H B K := by
    intro u v huv
    have huS := hS u v huv
    have hvS := hS v u huv.symm
    rw [← hcov] at huS hvS
    by_cases huA : u ∈ A
    · by_cases hvA : v ∈ A
      · exact Or.inl ⟨huA, hvA, Or.inl huv⟩
      · have hvB := (Finset.mem_union.1 hvS).resolve_left hvA
        by_cases huB : u ∈ B
        · exact Or.inr ⟨huB, hvB, Or.inl huv⟩
        · exact absurd huv (hnc u huA huB v hvB hvA)
    · have huB := (Finset.mem_union.1 huS).resolve_left huA
      by_cases hvB : v ∈ B
      · exact Or.inr ⟨huB, hvB, Or.inl huv⟩
      · have hvA := (Finset.mem_union.1 hvS).resolve_right hvB
        exact absurd huv.symm (hnc v hvA hvB u huB huA)
  refine IsPlanar.mono ?_ hle
  -- glue the two plane pieces along the separator
  by_cases h1 : K.card ≤ 1
  · exact isPlanar_sup_of_le_one hsA hsB MA MB fun p hp q hq => Finset.card_le_one.1 h1 p hp q hq
  · obtain ⟨x, y, hxy, hxyK⟩ := Finset.card_eq_two.1 (by omega : K.card = 2)
    have hxK : x ∈ K := by rw [hxyK]; simp
    have hyK : y ∈ K := by rw [hxyK]; simp
    exact isPlanar_sup_of_two hsA hsB MA MB hxy hxyK
      ⟨(Finset.mem_inter.1 hxK).1, (Finset.mem_inter.1 hyK).1, Or.inr ⟨hxK, hyK, hxy⟩⟩
      ⟨(Finset.mem_inter.1 hxK).2, (Finset.mem_inter.1 hyK).2, Or.inr ⟨hxK, hyK, hxy⟩⟩

omit [DecidableEq V] in
/-- **Wagner's theorem, reverse direction.**  Every finite graph with neither a `K_5` minor
nor a `K_{3,3}` minor is planar (rotation-system model `IsPlanar`).  No connectivity is
assumed. -/
theorem isPlanar_of_k5MinorFree_of_k33MinorFree (G : SimpleGraph V) (h5 : K5MinorFree G)
    (h33 : K33MinorFree G) : IsPlanar G := by
  have := Fintype.ofFinite V
  exact isPlanar_of_minorFree_aux _ G Finset.univ rfl (fun _ _ _ => Finset.mem_univ _) h5 h33

omit [DecidableEq V] in
/-- **Wagner's planarity criterion** (both directions): a finite graph is planar (rotation-system
model) iff it has neither a `K_5` minor nor a `K_{3,3}` minor. -/
theorem isPlanar_iff_k5MinorFree_and_k33MinorFree (G : SimpleGraph V) :
    IsPlanar G ↔ K5MinorFree G ∧ K33MinorFree G :=
  ⟨fun h => ⟨cliqueMinorFree_five_of_isPlanar h, k33MinorFree_of_isPlanar h⟩,
    fun h => isPlanar_of_k5MinorFree_of_k33MinorFree G h.1 h.2⟩

end LeanPool.K5MinorFreeChoosability
