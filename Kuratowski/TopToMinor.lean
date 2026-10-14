/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Kuratowski.Defs

/-!
# A topological minor is a minor

Orient every edge of `H` (for instance through an injection of `W` into `ℕ`, or a well-order).
The branch set of `w` is its branch vertex together with the vertices of the paths of the edges
oriented away from `w`, without their last vertex. These sets are connected (each is a union of
path prefixes through the branch vertex), pairwise disjoint (paths of different edges meet only at
branch vertices, and a path contains no branch vertex other than its ends), and for an edge
oriented from `w` to `w'` the last edge of its path joins the branch sets of `w` and `w'`.
-/

@[expose] public section

open SimpleGraph

namespace Kuratowski

variable {V W : Type*}

private theorem penultimate_mem {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.penultimate ∈ p.support := by
  unfold Walk.penultimate
  exact Walk.getVert_mem_support _ _

private theorem end_not_mem_takeUntil [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (hp : p.IsPath) (hx : x ∈ p.support) (hxv : x ≠ v) :
    v ∉ (p.takeUntil x hx).support := by
  intro hv
  have hnd := hp.support_nodup
  rw [← p.take_spec hx, Walk.support_append] at hnd
  have hne : ¬ (p.dropUntil x hx).Nil := Walk.not_nil_of_ne hxv
  have := Walk.end_mem_tail_support hne
  exact (List.nodup_append.mp hnd).2.2 _ hv _ this rfl

open Classical in
/-- The branch set of `w` built from a subdivision. -/
private noncomputable def topBranch [DecidableEq V] [Fintype W] [LinearOrder W]
    {G : SimpleGraph V} {H : SimpleGraph W} (M : TopologicalMinorModel G H) (w : W) : Finset V :=
  insert (M.vertex w) ((Finset.univ.filter (fun w' => w < w')).biUnion fun w' =>
    if h : H.Adj w w' then (M.path w w' h).support.toFinset.erase (M.vertex w') else ∅)

private theorem mem_topBranch [DecidableEq V] [Fintype W] [LinearOrder W]
    {G : SimpleGraph V} {H : SimpleGraph W} (M : TopologicalMinorModel G H) (w : W) (x : V) :
    x ∈ topBranch M w ↔ x = M.vertex w ∨
      ∃ w', ∃ h : H.Adj w w', w < w' ∧ x ∈ (M.path w w' h).support ∧ x ≠ M.vertex w' := by
  unfold topBranch
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨w', hlt, hx⟩
    by_cases h : H.Adj w w'
    · simp only [h, dite_true, Finset.mem_erase, List.mem_toFinset] at hx
      exact ⟨w', h, hlt, hx.2, hx.1⟩
    · simp [h] at hx
  · rintro ⟨w', h, hlt, hx, hne⟩
    refine ⟨w', hlt, ?_⟩
    simp [h, hx, hne]

private theorem reach_of_walk {G : SimpleGraph V} (S : Set V) {u v : V} (p : G.Walk u v)
    (hp : ∀ x ∈ p.support, x ∈ S) :
    (G.induce S).Reachable ⟨u, hp u p.start_mem_support⟩ ⟨v, hp v p.end_mem_support⟩ :=
  ⟨p.induce S hp⟩

/-- A topological minor is a minor. -/
theorem TopologicalMinorModel.isMinor [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (M : TopologicalMinorModel G H) : IsMinor H G := by
  classical
  have := Fintype.ofFinite W
  let _ : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  have hmem := mem_topBranch M
  have hbase : ∀ w, M.vertex w ∈ topBranch M w := fun w => (hmem w _).2 (Or.inl rfl)
  refine ⟨⟨topBranch M, fun w => ⟨_, hbase w⟩, ?_, ?_, ?_⟩⟩
  · intro w
    have hreach : ∀ x (hx : x ∈ (topBranch M w : Set V)),
        (G.induce (topBranch M w : Set V)).Reachable ⟨M.vertex w, hbase w⟩ ⟨x, hx⟩ := by
      intro x hx
      rcases (hmem w x).1 hx with rfl | ⟨w', h, hlt, hxs, hne⟩
      · rfl
      · have hsub : ∀ y ∈ ((M.path w w' h).takeUntil x hxs).support,
            y ∈ (topBranch M w : Set V) := by
          intro y hy
          refine (hmem w y).2 (Or.inr ⟨w', h, hlt,
            Walk.support_takeUntil_subset_support _ _ hy, ?_⟩)
          rintro rfl
          exact end_not_mem_takeUntil _ (M.path_isPath w w' h) hxs hne hy
        exact reach_of_walk _ _ hsub
    have : Nonempty (topBranch M w : Set V) := ⟨⟨_, hbase w⟩⟩
    exact ⟨fun a b => (hreach a.1 a.2).symm.trans (hreach b.1 b.2)⟩
  · intro w w' hww'
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases (hmem w x).1 hx with hx1 | ⟨u, h, hlt, hxs, hne⟩ <;>
      rcases (hmem w' x).1 hx' with hx2 | ⟨u', h', hlt', hxs', hne'⟩
    · exact hww' (M.vertex.injective (hx1.symm.trans hx2))
    · subst hx1
      rcases M.path_branch w' u' h' w hxs' with h1 | h1
      · exact hww' h1
      · exact hne' (h1 ▸ rfl)
    · subst hx2
      rcases M.path_branch w u h w' hxs with h1 | h1
      · exact hww' h1.symm
      · exact hne (h1 ▸ rfl)
    · have hs : s(w, u) ≠ s(w', u') := by
        intro hs
        rcases Sym2.eq_iff.mp hs with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact hww' h1
        · subst h1; subst h2
          exact absurd (hlt.trans hlt') (lt_irrefl _)
      obtain ⟨z, rfl⟩ := M.path_disjoint w u h w' u' h' hs x hxs hxs'
      rcases M.path_branch w u h z hxs with h1 | h1
      · rcases M.path_branch w' u' h' z hxs' with h2 | h2
        · exact hww' (h1.symm.trans h2)
        · exact hne' (h2 ▸ rfl)
      · exact hne (h1 ▸ rfl)
  · have key : ∀ w w', H.Adj w w' → w < w' →
        ∃ u ∈ topBranch M w, ∃ v ∈ topBranch M w', G.Adj u v := by
      intro w w' h hlt
      have hne : M.vertex w ≠ M.vertex w' := fun e => H.ne_of_adj h (M.vertex.injective e)
      have hnil := Walk.not_nil_of_ne (p := M.path w w' h) hne
      refine ⟨_, (hmem w _).2 (Or.inr ⟨w', h, hlt, penultimate_mem _, ?_⟩), _, hbase w',
        Walk.adj_penultimate hnil⟩
      exact (Walk.adj_penultimate hnil).ne
    intro w w' h
    rcases lt_or_gt_of_ne (H.ne_of_adj h) with hlt | hlt
    · exact key w w' h hlt
    · obtain ⟨u, hu, v, hv, huv⟩ := key w' w h.symm hlt
      exact ⟨v, hv, u, hu, huv.symm⟩

end Kuratowski
