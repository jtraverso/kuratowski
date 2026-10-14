/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Thomassen
public import LeanPool.K5MinorFreeChoosability.Wagner.Contractible
public import LeanPool.K5MinorFreeChoosability.Wagner.CyclicWord
public import LeanPool.K5MinorFreeChoosability.Wagner.PrimeLeafAttack
public import LeanPool.K5MinorFreeChoosability.Wagner.PlanarLeaves

/-!
# Kuratowski's theorem for graphs without small separations (prime-leaf planarity)

`isPlanar_of_noSmallSep`: a finite graph whose edges lie in a vertex set `S` without separations
of order at most two, and which has neither a `K_5` nor a `K_{3,3}` minor, is planar in the
rotation-system model `IsPlanar`.  This is Thomassen's proof: contract an edge `xy` keeping
`NoSmallSep` (`exists_contractible_edge_of_noSmallSep`), embed the contraction by induction, and
read the neighbours of `x` and `y` around the contracted vertex (`cyclic_trichotomy`).  Three common
neighbours give a `K_5` minor, an alternating pattern gives a `K_{3,3}` minor, and otherwise the
vertex can be split (`isPlanar_of_good`).

Consequences:

* `primeLeafPlanarity`: the obligation `PrimeLeafPlanarity H` of `PlanarLeaves` holds for every
  finite graph;
* `exists_k33DecompPlanar`: the planar-leaf decomposition of a `K_{3,3}`-minor-free graph exists
  unconditionally.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*} [DecidableEq V]

/-- In a vertex set with at least four vertices and no separation of order at most two, every
vertex has a neighbour outside any set of at most two vertices. -/
theorem exists_adj_not_mem_of_noSmallSep {H : SimpleGraph V} {S : Finset V}
    (hsep : NoSmallSep H S) (h4 : 4 ≤ S.card) {v : V} (hv : v ∈ S) (Z : Finset V)
    (hZ : Z.card ≤ 2) : ∃ u, u ∉ Z ∧ H.Adj v u := by
  by_contra hn
  push Not at hn
  set Z0 := (Z.erase v) ∩ S with hZ0def
  have hZ0 : Z0.card ≤ 2 :=
    (Finset.card_le_card (Finset.inter_subset_left.trans (Finset.erase_subset _ _))).trans hZ
  have hside : IsSide H S Z0 {v} := by
    refine ⟨Finset.singleton_subset_iff.2 hv, ?_, Finset.singleton_nonempty v, ?_, ?_⟩
    · exact Finset.disjoint_singleton_left.2 (fun h => by simp [Z0] at h)
    · rw [Finset.sdiff_nonempty]
      intro hsub
      have := Finset.card_le_card hsub
      have h1 := Finset.card_union_le {v} Z0
      rw [Finset.card_singleton] at h1
      omega
    · intro p hp q hq hqR hqZ hpq
      rw [Finset.mem_singleton] at hp hqR
      subst hp
      by_cases hqZ' : q ∈ Z
      · exact hqZ (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hqR, hqZ'⟩, hq⟩)
      · exact hn q hqZ' hpq
  exact hside.false hsep Finset.inter_subset_right hZ0

variable [Finite V]

theorem isPlanar_of_noSmallSep_aux (n : ℕ) : ∀ (H : SimpleGraph V) (S : Finset V), S.card = n →
    (∀ u v, H.Adj u v → u ∈ S) → NoSmallSep H S → K5MinorFree H → K33MinorFree H →
    IsPlanar H := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H S hn hS hsep h5 h33
  by_cases hsmall : S.card ≤ 4
  · exact isPlanar_of_card_le_four hS hsmall
  push Not at hsmall
  obtain ⟨x, y, hxy, hsepc⟩ := exists_contractible_edge_of_noSmallSep hS hsep (by omega)
  have hxS : x ∈ S := hS x y hxy
  have hyS : y ∈ S := hS y x hxy.symm
  have hSc : ∀ u v, (contractGraph H x y).Adj u v → u ∈ S.erase y :=
    fun u v h => contractGraph_support hS hxy h
  have hcard : (S.erase y).card < n := by
    rw [Finset.card_erase_of_mem hyS]
    omega
  obtain ⟨M⟩ := ih _ hcard (contractGraph H x y) (S.erase y) rfl hSc hsepc
    (k5MinorFree_contractGraph hxy h5) (k33MinorFree_contractGraph hxy h33)
  have hK : numComponents M.rot (dartSymm _) ≤ 1 := by
    have hc := hsepc.connSet_sdiff (Z := ∅) (Finset.empty_subset _) (by simp)
      ⟨x, by simp [hxy.ne, hxS]⟩
    rw [Finset.sdiff_empty] at hc
    exact numComponents_le_one_of_connSet M.isRotationSystem hSc hc
  -- two neighbours of `x` other than `y`
  obtain ⟨w1, hw1, hxw1⟩ :=
    exists_adj_not_mem_of_noSmallSep hsep (by omega) hxS {y} (by simp)
  obtain ⟨w2, hw2, hxw2⟩ :=
    exists_adj_not_mem_of_noSmallSep hsep (by omega) hxS {y, w1} Finset.card_le_two
  rw [Finset.mem_singleton] at hw1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw2
  have hc1 : (contractGraph H x y).Adj x w1 :=
    (contractGraph_adj_x hxy.ne).2 ⟨hxw1.ne.symm, hw1, Or.inl hxw1⟩
  have hc2 : (contractGraph H x y).Adj x w2 :=
    (contractGraph_adj_x hxy.ne).2 ⟨hxw2.ne.symm, hw2.1, Or.inl hxw2⟩
  set e0 : (contractGraph H x y).Dart := ⟨(x, w1), hc1⟩ with he0def
  have he0 : e0.fst = x := rfl
  set k := M.rper e0 with hk
  obtain ⟨i2, -, hrd2⟩ := M.exists_rd_eq e0 (d := ⟨(x, w2), hc2⟩) rfl
  have hw12 : ∀ j, M.rd e0 j = e0 → M.rd e0 j ≠ ⟨(x, w2), hc2⟩ := by
    intro j h1 h2
    have := congrArg (fun d : (contractGraph H x y).Dart => d.snd) (h1.symm.trans h2)
    exact hw2.2 this.symm
  have h2 : 2 ≤ k := by
    by_contra hk2
    have hk1 : k = 1 := by have := M.rper_pos e0; omega
    have hrd : M.rd e0 i2 = e0 := by
      rw [← M.rd_mod, ← hk, hk1, Nat.mod_one, M.rd_zero]
    exact hw12 i2 hrd hrd2
  have hrdx : ∀ i, (contractGraph H x y).Adj x (M.rd e0 i).snd := by
    intro i
    have := (M.rd e0 i).adj
    rwa [M.rd_fst] at this
  have hper : ∀ i, (H.Adj x (M.rd e0 (i + k)).snd ↔ H.Adj x (M.rd e0 i).snd) ∧
      (H.Adj y (M.rd e0 (i + k)).snd ↔ H.Adj y (M.rd e0 i).snd) := by
    intro i
    rw [hk, M.rd_add_rper]
    exact ⟨Iff.rfl, Iff.rfl⟩
  have hcov : ∀ i, H.Adj x (M.rd e0 i).snd ∨ H.Adj y (M.rd e0 i).snd :=
    fun i => ((contractGraph_adj_x hxy.ne).1 (hrdx i)).2.2
  have hpos : ∀ s, ∃ t, 1 ≤ t ∧ t < k ∧ H.Adj x (M.rd e0 (s + t)).snd := by
    intro s
    obtain ⟨t1, ht1, h1⟩ := M.exists_window e0 s 0
    obtain ⟨t2, ht2, h2'⟩ := M.exists_window e0 s i2
    rw [M.rd_zero] at h1
    rw [hrd2] at h2'
    by_cases ht10 : t1 = 0
    · refine ⟨t2, ?_, ht2, by rw [h2']; exact hxw2⟩
      by_contra ht20
      have : t2 = 0 := by omega
      subst this
      subst ht10
      exact hw12 (s + 0) h1 h2'
    · exact ⟨t1, by omega, ht1, by rw [h1]; exact hxw1⟩
  rcases cyclic_trichotomy k (fun i => H.Adj x (M.rd e0 i).snd)
      (fun i => H.Adj y (M.rd e0 i).snd) hper hcov hpos with
    ⟨a, b, c, hab, hbc, hca, ha, hb, hc⟩ | ⟨a, b, c, d, hab, hbc, hcd, hda, ha, hb, hc, hd⟩ |
      ⟨s, ℓ, hℓ, hA, hB⟩
  · exact absurd h5 (not_k5MinorFree_of_three M e0 hSc hsepc hK he0 h2 hxy hab hbc hca
      ha.1 ha.2 hb.1 hb.2 hc.1 hc.2)
  · exact absurd (isMinor_K33_of_alternating M e0 hSc hsepc hK he0 h2 hxy hab hbc hcd hda
      ha hb hc hd) h33
  · exact isPlanar_of_good hxy M e0 he0 hℓ (fun t h1 h2 => (hA t h1 h2).2) hB

/-- **Kuratowski's theorem for prime pieces.**  A finite graph whose edges lie in a vertex set
`S` without separations of order at most two, and which has neither a `K_5` minor nor a
`K_{3,3}` minor, has a plane embedding (genus-zero rotation system). -/
theorem isPlanar_of_noSmallSep {H : SimpleGraph V} {S : Finset V}
    (hS : ∀ u v, H.Adj u v → u ∈ S) (hsep : NoSmallSep H S) (h5 : K5MinorFree H)
    (h33 : K33MinorFree H) : IsPlanar H :=
  isPlanar_of_noSmallSep_aux _ H S rfl hS hsep h5 h33

/-- **Prime-leaf planarity**, unconditionally: the obligation isolated in `PlanarLeaves` holds
for every finite graph. -/
theorem primeLeafPlanarity (H : SimpleGraph V) : PrimeLeafPlanarity H :=
  fun _ h5 h33 hsep => isPlanar_of_noSmallSep (fun _ _ h => Finset.mem_coe.1 h.2.1) hsep h5 h33

omit [Finite V] in
/-- **Planar-leaf decomposition, unconditional**: every finite `K_{3,3}`-minor-free graph is a
spanning subgraph of a graph with a planar-leaf certificate (leaves small or planar, glued along
retained cliques of order at most two). -/
theorem exists_k33DecompPlanar [Fintype V] (G : SimpleGraph V) (hG : K33MinorFree G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ K33DecompPlanar H Finset.univ :=
  exists_k33DecompPlanar_of_primeLeafPlanarity (fun H => primeLeafPlanarity H) G hG

end LeanPool.K5MinorFreeChoosability
