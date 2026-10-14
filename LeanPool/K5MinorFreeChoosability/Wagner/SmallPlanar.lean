/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.HypermapKit
public import LeanPool.K5MinorFreeChoosability.Planar.Examples
public import LeanPool.K5MinorFreeChoosability.Planar.MinorClosed

/-!
# Transport of plane maps and small planar graphs

* `isPlanar_map`: planarity is preserved by pushing a graph forward along an injective map of
  vertex types (the new vertices are isolated);
* `isPlanar_of_card_le_four`: a graph all of whose edges lie in a set of at most four vertices
  is planar;
* `numComponents_le_one_of_connSet`: a rotation system of a graph whose edges lie in a connected
  vertex set has at most one component.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V W : Type*}

/-- The image of a dart under an injective map of vertices. -/
def mapDart (f : W ↪ V) (G : SimpleGraph W) (d : G.Dart) : (G.map f).Dart :=
  ⟨(f d.fst, f d.snd), (SimpleGraph.map_adj f G _ _).2 ⟨d.fst, d.snd, d.adj, rfl, rfl⟩⟩

theorem mapDart_bijective (f : W ↪ V) (G : SimpleGraph W) : Function.Bijective (mapDart f G) := by
  constructor
  · intro d e h
    have h1 : f d.fst = f e.fst := congrArg (fun z : (G.map f).Dart => z.fst) h
    have h2 : f d.snd = f e.snd := congrArg (fun z : (G.map f).Dart => z.snd) h
    exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext (f.injective h1) (f.injective h2))
  · intro d
    obtain ⟨u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj f G _ _).1 d.adj
    refine ⟨⟨(u, v), huv⟩, ?_⟩
    refine (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext ?_ ?_)
    · exact hu
    · exact hv

/-- Planarity is preserved by an injective change of vertex type. -/
theorem isPlanar_map [Finite V] [Finite W] {G : SimpleGraph W} (f : W ↪ V) (hG : IsPlanar G) :
    IsPlanar (G.map f) := by
  classical
  obtain ⟨P⟩ := hG
  have := Fintype.ofFinite W
  refine isPlanar_of_hypermap P.rot (dartSymm G) P.eulerDefect_eq_zero.le (mapDart f G)
    (mapDart_bijective f G) (fun d => rfl) (fun d => ?_) ?_
  · change f (P.rot d).fst = f d.fst
    rw [P.isRotationSystem.fst_apply]
  · rw [cycleCount_eq_card_nonisolated P.isRotationSystem]
    refine Nat.card_le_card_of_injective (fun v => ⟨f v.1, ?_⟩) ?_
    · obtain ⟨u, hu⟩ := v.2
      exact ⟨f u, (SimpleGraph.map_adj f G _ _).2 ⟨v.1, u, hu, rfl, rfl⟩⟩
    · intro a b h
      exact Subtype.ext (f.injective (congrArg Subtype.val h))

/-- A graph whose edges lie in a set of at most four vertices is planar. -/
theorem isPlanar_of_card_le_four [Finite V] {H : SimpleGraph V} {S : Finset V}
    (hS : ∀ u v, H.Adj u v → u ∈ S) (h4 : S.card ≤ 4) : IsPlanar H := by
  classical
  let f : (↑S : Set V) ↪ V := Function.Embedding.subtype _
  have hH : (H.induce (↑S : Set V)).map f = H := by
    ext u v
    rw [SimpleGraph.map_adj]
    constructor
    · rintro ⟨u', v', h, rfl, rfl⟩
      exact h
    · intro h
      exact ⟨⟨u, hS u v h⟩, ⟨v, hS v u h.symm⟩, h, rfl, rfl⟩
  rw [← hH]
  refine isPlanar_map f (IsPlanar.of_isMinor isPlanar_K4 ?_)
  have hcard : Fintype.card (↑S : Set V) ≤ Fintype.card (Fin 4) := by
    simpa using h4
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨⟨fun w => {g w}, fun w => Finset.singleton_nonempty _, fun w => ?_, fun w w' h => ?_,
    fun w w' h => ?_⟩⟩
  · rw [← connSet_iff_induce_connected, Finset.coe_singleton]
    exact connSet_singleton _ _
  · exact Finset.disjoint_singleton.2 (fun e => h (g.injective e))
  · refine ⟨g w, Finset.mem_singleton_self _, g w', Finset.mem_singleton_self _, ?_⟩
    exact fun e => h.ne (g.injective e)

/-- A rotation system of a graph whose edges lie in a connected vertex set has at most one
component. -/
theorem numComponents_le_one_of_connSet [Finite V] {G : SimpleGraph V} {σ : Perm G.Dart}
    {S : Finset V} (hσ : IsRotationSystem G σ) (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hc : ConnSet G ↑S) : numComponents σ (dartSymm G) ≤ 1 := by
  have key : ∀ a b, RIn G ↑S a b → ∀ d e : G.Dart, d.fst = a → e.fst = b →
      compSetoid σ (dartSymm G) d e := by
    intro a b h
    induction h with
    | refl => exact fun d e hd he =>
        compSetoid_of_sameCycle_left (hσ.sameCycle d e (hd.trans he.symm))
    | @tail c b _ hcb ih =>
      intro d e hd he
      let x : G.Dart := ⟨(c, b), hcb.1⟩
      have h1 := ih d x hd rfl
      have h2 : compSetoid σ (dartSymm G) x x.symm := compSetoid_right _ _ x
      have h3 : compSetoid σ (dartSymm G) x.symm e :=
        compSetoid_of_sameCycle_left (hσ.sameCycle _ _ he.symm)
      exact (compSetoid _ _).trans h1 ((compSetoid _ _).trans h2 h3)
  have hsub : Subsingleton (Quotient (compSetoid σ (dartSymm G))) := by
    constructor
    intro p q
    induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    exact Quotient.sound (key _ _ (hc.2 _ (hS _ _ a.adj) _ (hS _ _ b.adj)) a b rfl rfl)
  exact Finite.card_le_one_iff_subsingleton.2 hsub

end LeanPool.K5MinorFreeChoosability
