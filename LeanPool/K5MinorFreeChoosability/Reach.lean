/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Basic
public import Mathlib

/-!
# Reachability inside a vertex set

`RIn G s a b` says that `b` can be reached from `a` by a walk of `G` all of whose
edges have both ends in `s`.  `ConnSet G s` says that `s` is a nonempty set inducing a
connected subgraph.  We prove that `ConnSet` agrees with Mathlib's
`(G.induce s).Connected`, together with the basic manipulation lemmas used by the
separation arguments of the Wood--Linusson proof.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {W : Type*}

/-- Reachability using only edges with both ends in `s`. -/
def RIn (G : SimpleGraph W) (s : Set W) : W → W → Prop :=
  Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s)

/-- A nonempty vertex set inducing a connected subgraph. -/
def ConnSet (G : SimpleGraph W) (s : Set W) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, RIn G s a b

/-- The graph `G` with all edges leaving `s` removed. -/
def restrict (G : SimpleGraph W) (s : Set W) : SimpleGraph W where
  Adj a b := G.Adj a b ∧ a ∈ s ∧ b ∈ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[simp] theorem restrict_adj {G : SimpleGraph W} {s : Set W} {a b : W} :
    (restrict G s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s := Iff.rfl

theorem restrict_le (G : SimpleGraph W) (s : Set W) : restrict G s ≤ G :=
  fun _ _ h => h.1

namespace RIn

variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}

@[refl] theorem refl (a : W) : RIn G s a a := Relation.ReflTransGen.refl

theorem trans (h₁ : RIn G s a b) (h₂ : RIn G s b c) : RIn G s a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem single (h : G.Adj a b) (ha : a ∈ s) (hb : b ∈ s) : RIn G s a b :=
  Relation.ReflTransGen.single ⟨h, ha, hb⟩

theorem tail (h₁ : RIn G s a b) (h : G.Adj b c) (hb : b ∈ s) (hc : c ∈ s) : RIn G s a c :=
  Relation.ReflTransGen.tail h₁ ⟨h, hb, hc⟩

theorem head (h : G.Adj a b) (ha : a ∈ s) (hb : b ∈ s) (h₁ : RIn G s b c) : RIn G s a c :=
  Relation.ReflTransGen.head ⟨h, ha, hb⟩ h₁

theorem symm (h : RIn G s a b) : RIn G s b a := by
  induction h with
  | refl => exact refl _
  | tail _ hbc ih => exact head hbc.1.symm hbc.2.2 hbc.2.1 ih

theorem mono (h : RIn G s a b) (hG : G ≤ G') (hs : s ⊆ t) : RIn G' t a b := by
  induction h with
  | refl => exact refl _
  | tail _ hbc ih => exact ih.tail (hG hbc.1) (hs hbc.2.1) (hs hbc.2.2)

theorem mono_set (h : RIn G s a b) (hs : s ⊆ t) : RIn G t a b := h.mono le_rfl hs

theorem mono_graph (h : RIn G s a b) (hG : G ≤ G') : RIn G' s a b := h.mono hG subset_rfl

theorem mem (h : RIn G s a b) (ha : a ∈ s) : b ∈ s := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.2

/-- Transport of reachability along a map sending each relevant edge to a reachable pair. -/
theorem map {W' : Type*} {G' : SimpleGraph W'} {t : Set W'} (f : W → W')
    (hf : ∀ x y, G.Adj x y → x ∈ s → y ∈ s → RIn G' t (f x) (f y))
    (h : RIn G s a b) : RIn G' t (f a) (f b) := by
  induction h with
  | refl => exact refl _
  | tail _ hbc ih => exact ih.trans (hf _ _ hbc.1 hbc.2.1 hbc.2.2)

/-- Walks starting inside the set `P` and ending outside of it must leave `P` along an edge. -/
theorem exit {P : Set W} (h : RIn G s a b) (haP : a ∈ P) (hbP : b ∉ P) :
    ∃ p q, RIn G (s ∩ P) a p ∧ p ∈ s ∧ p ∈ P ∧ q ∈ s ∧ q ∉ P ∧ G.Adj p q := by
  have key : (∃ p q, RIn G (s ∩ P) a p ∧ p ∈ s ∧ p ∈ P ∧ q ∈ s ∧ q ∉ P ∧ G.Adj p q) ∨
      (b ∈ P ∧ RIn G (s ∩ P) a b) := by
    clear hbP
    induction h with
    | refl => exact Or.inr ⟨haP, refl _⟩
    | @tail c d _ hcd ih =>
      rcases ih with hex | ⟨hc, hac⟩
      · exact Or.inl hex
      · by_cases hd : d ∈ P
        · exact Or.inr ⟨hd, hac.tail hcd.1 ⟨hcd.2.1, hc⟩ ⟨hcd.2.2, hd⟩⟩
        · exact Or.inl ⟨c, d, hac, hcd.2.1, hc, hcd.2.2, hd, hcd.1⟩
  rcases key with hex | ⟨hb, _⟩
  · exact hex
  · exact absurd hb hbP

/-- A walk from `a` that never meets the reachability class of a forbidden vertex avoids it:
if `t` is not reachable from `a` inside `s`, then reachability inside `s` agrees with
reachability inside `s \ {t}` for walks starting at `a`. -/
theorem avoid (h : RIn G s a b) {t : W} (ht : ¬ RIn G s a t) : RIn G (s \ {t}) a b := by
  induction h with
  | refl => exact refl _
  | @tail c d hac hcd ih =>
    have hc : c ≠ t := fun hct => ht (hct ▸ hac)
    have hd : d ≠ t := fun hdt => ht (hdt ▸ RIn.tail hac hcd.1 hcd.2.1 hcd.2.2)
    exact ih.tail hcd.1 ⟨hcd.2.1, hc⟩ ⟨hcd.2.2, hd⟩

/-- Two vertices `a, b` of `s` with a path of length at most one inside `{a, b}`. -/
theorem adj_of_pair (h : RIn G {a, b} a b) (hab : a ≠ b) : G.Adj a b := by
  obtain ⟨p, q, _, _, hp, hq, hqP, hpq⟩ :=
    h.exit (P := {a}) (by simp) (by simpa using hab.symm)
  simp only [Set.mem_singleton_iff] at hp hqP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  subst hp
  rcases hq with rfl | rfl
  · exact absurd rfl hqP
  · exact hpq

end RIn

theorem connSet_iff_induce_connected (G : SimpleGraph W) (s : Set W) :
    ConnSet G s ↔ (G.induce s).Connected := by
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    have : Nonempty s := ⟨⟨a, ha⟩⟩
    refine SimpleGraph.Connected.mk ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hxy := h x hx y hy
    have key : ∀ z, RIn G s x z → ∀ hz : z ∈ s,
        (G.induce s).Reachable ⟨x, hx⟩ ⟨z, hz⟩ := by
      intro z hz
      induction hz with
      | refl => exact fun _ => SimpleGraph.Reachable.refl _
      | @tail c d _ hcd ih =>
        intro hd
        exact (ih hcd.2.1).trans (SimpleGraph.Adj.reachable (by simpa using hcd.1))
    exact key y hxy hy
  · intro h
    obtain ⟨⟨a, ha⟩⟩ := h.nonempty
    refine ⟨⟨a, ha⟩, fun x hx y hy => ?_⟩
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (h.preconnected ⟨x, hx⟩ ⟨y, hy⟩)
    have := Relation.ReflTransGen.lift (p := fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s)
      Subtype.val (fun u v huv => ⟨by simpa using huv, u.2, v.2⟩) _ _ hr
    exact this

theorem ConnSet.mono {G G' : SimpleGraph W} {s : Set W} (h : ConnSet G s) (hG : G ≤ G') :
    ConnSet G' s :=
  ⟨h.1, fun a ha b hb => (h.2 a ha b hb).mono_graph hG⟩

theorem connSet_singleton (G : SimpleGraph W) (a : W) : ConnSet G {a} :=
  ⟨⟨a, rfl⟩, fun x hx y hy => by
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy; exact RIn.refl _⟩

/-- Adding a vertex adjacent to a connected set keeps it connected. -/
theorem ConnSet.insert_adj {G : SimpleGraph W} {s : Set W} (h : ConnSet G s) {a b : W}
    (hb : b ∈ s) (hab : G.Adj a b) : ConnSet G (insert a s) := by
  have hsub : s ⊆ insert a s := Set.subset_insert _ _
  have ha : ∀ x ∈ s, RIn G (insert a s) a x := fun x hx =>
    RIn.head hab (Set.mem_insert _ _) (hsub hb) ((h.2 b hb x hx).mono_set hsub)
  refine ⟨⟨a, Set.mem_insert _ _⟩, fun x hx y hy => ?_⟩
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact RIn.refl _
  · exact ha y hy
  · exact (ha x hx).symm
  · exact (h.2 x hx y hy).mono_set hsub

/-- The vertices reachable from `a` inside `s` form a connected set. -/
theorem connSet_reach (G : SimpleGraph W) (s : Set W) {a : W} (ha : a ∈ s) :
    ConnSet G {x | x ∈ s ∧ RIn G s a x} := by
  have key : ∀ x, RIn G s a x → RIn G {x | x ∈ s ∧ RIn G s a x} a x := by
    intro x hx
    induction hx with
    | refl => exact RIn.refl _
    | @tail c d hac hcd ih =>
      exact RIn.tail ih hcd.1 ⟨hcd.2.1, hac⟩ ⟨hcd.2.2, RIn.tail hac hcd.1 hcd.2.1 hcd.2.2⟩
  exact ⟨⟨a, ha, RIn.refl _⟩, fun x hx y hy => (key x hx.2).symm.trans (key y hy.2)⟩

end LeanPool.K5MinorFreeChoosability
