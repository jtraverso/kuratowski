/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Reach

/-!
# Transport of complete minors

We prove the minor-theoretic facts used by the Wood--Linusson argument, phrased directly
with connected branch sets (`CliqueMinorModel`):

* `cliqueMinorFree_of_transport`: if every vertex of `H` that carries an edge is sent to a
  nonempty connected branch set of `G`, different vertices to disjoint sets, and edges of
  `H` to edges of `G` between the corresponding sets (that is, `H` is a minor of `G`),
  then a complete minor of `H` yields one of `G`;
* monotonicity under subgraphs;
* `cliqueMinorFree_of_cliqueSum`: a clique-sum of two graphs without a `K_k` minor has no
  `K_k` minor;
* graphs whose edges lie in fewer than `k` vertices have no `K_k` minor.

We also define the apex extension `apexExtend G B` with its fresh vertex `none`.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {W W' : Type*}

section Models

variable {G H : SimpleGraph W} {k : ℕ}

theorem CliqueMinorModel.connSet (M : CliqueMinorModel G k) (i : Fin k) :
    ConnSet G ↑(M.branch i) :=
  (connSet_iff_induce_connected _ _).2 (M.branch_connected i)

/-- Build a complete minor model from branch sets that are connected in the sense of
`ConnSet`. -/
def CliqueMinorModel.ofConnSet (branch : Fin k → Finset W)
    (hc : ∀ i, ConnSet G ↑(branch i))
    (hd : ∀ i j, i ≠ j → Disjoint (branch i) (branch j))
    (ha : ∀ i j, i ≠ j → ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v) :
    CliqueMinorModel G k where
  branch := branch
  branch_nonempty i := by
    obtain ⟨x, hx⟩ := (hc i).1
    exact ⟨x, hx⟩
  branch_connected i := (connSet_iff_induce_connected _ _).1 (hc i)
  branch_disjoint := hd
  branch_adjacent := ha

theorem exists_ne_fin (hk : 2 ≤ k) (i : Fin k) : ∃ j : Fin k, j ≠ i := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  exact exists_ne i

/-- When `k ≥ 2`, every vertex of a branch set of a `K_k` model lies in any set containing
all endpoints of edges. -/
theorem CliqueMinorModel.mem_of_edges (M : CliqueMinorModel H k) (hk : 2 ≤ k) (T : Set W)
    (hT : ∀ x y, H.Adj x y → x ∈ T) (i : Fin k) {x : W} (hx : x ∈ M.branch i) : x ∈ T := by
  obtain ⟨j, hji⟩ := exists_ne_fin hk i
  obtain ⟨u, hu, v, _, huv⟩ := M.branch_adjacent i j hji.symm
  have hr := (M.connSet i).2 u hu x hx
  have huT : u ∈ T := hT u v huv
  clear hu hx
  induction hr with
  | refl => exact huT
  | @tail c d _ hcd _ => exact hT d c hcd.1.symm

end Models

section Transport

variable {H : SimpleGraph W'} {G : SimpleGraph W} {k : ℕ}

theorem connSet_biUnion [DecidableEq W] (T : Set W') (φ : W' → Finset W)
    (hconn : ∀ x ∈ T, ConnSet G ↑(φ x))
    (hadj : ∀ x y, H.Adj x y → ∃ a ∈ φ x, ∃ b ∈ φ y, G.Adj a b)
    (X : Finset W') (hX : ConnSet H ↑X) (hXT : ∀ x ∈ X, x ∈ T) :
    ConnSet G ↑(X.biUnion φ) := by
  obtain ⟨x₀, hx₀⟩ := hX.1
  obtain ⟨a₀, ha₀⟩ := (hconn x₀ (hXT x₀ hx₀)).1
  have hsub : ∀ x ∈ X, (↑(φ x) : Set W) ⊆ ↑(X.biUnion φ) := by
    intro x hx a ha
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at ha ⊢
    exact ⟨x, hx, ha⟩
  have key : ∀ x ∈ X, ∀ a ∈ φ x, ∀ y, RIn H ↑X x y → y ∈ X → ∀ b ∈ φ y,
      RIn G ↑(X.biUnion φ) a b := by
    intro x hx a ha y hxy
    induction hxy with
    | refl =>
      intro _ b hb
      exact ((hconn x (hXT x hx)).2 a ha b hb).mono_set (hsub x hx)
    | @tail c d _ hcd ih =>
      intro hd b hb
      have hc : c ∈ X := hcd.2.1
      obtain ⟨a', ha', b', hb', hab'⟩ := hadj c d hcd.1
      have h1 := ih hc a' ha'
      have h2 := RIn.single (s := ↑(X.biUnion φ)) hab' (hsub c hc ha') (hsub d hd hb')
      have h3 := ((hconn d (hXT d hd)).2 b' hb' b hb).mono_set (hsub d hd)
      exact (h1.trans h2).trans h3
  refine ⟨⟨a₀, hsub x₀ hx₀ ha₀⟩, fun a ha b hb => ?_⟩
  simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, ha⟩ := ha
  obtain ⟨y, hy, hb⟩ := hb
  exact key x hx a ha y (hX.2 x hx y hy) hy b hb

/-- **Minor transport.**  If `H` is a minor of `G`, witnessed by the branch sets `φ x`
for the vertices `x` of `H` that carry edges, then a complete minor of `H` gives one of
`G`. -/
theorem nonempty_model_of_transport (hk : 2 ≤ k) (T : Set W')
    (hT : ∀ x y, H.Adj x y → x ∈ T) (φ : W' → Finset W)
    (hconn : ∀ x ∈ T, ConnSet G ↑(φ x))
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (φ x) (φ y))
    (hadj : ∀ x y, H.Adj x y → ∃ a ∈ φ x, ∃ b ∈ φ y, G.Adj a b)
    (M : CliqueMinorModel H k) : Nonempty (CliqueMinorModel G k) := by
  classical
  have hmem := M.mem_of_edges hk T hT
  refine ⟨CliqueMinorModel.ofConnSet (fun i => (M.branch i).biUnion φ) (fun i => ?_)
    (fun i j hij => ?_) (fun i j hij => ?_)⟩
  · exact connSet_biUnion T φ hconn hadj _ (M.connSet i) (fun x hx => hmem i hx)
  · rw [Finset.disjoint_biUnion_left]
    intro x hx
    rw [Finset.disjoint_biUnion_right]
    intro y hy
    have hxy : x ≠ y := by
      rintro rfl
      exact Finset.disjoint_left.1 (M.branch_disjoint i j hij) hx hy
    exact hdisj x (hmem i hx) y (hmem j hy) hxy
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
    obtain ⟨a, ha, b, hb, hab⟩ := hadj u v huv
    exact ⟨a, Finset.mem_biUnion.2 ⟨u, hu, ha⟩, b, Finset.mem_biUnion.2 ⟨v, hv, hb⟩, hab⟩

theorem cliqueMinorFree_of_transport (hk : 2 ≤ k) (T : Set W')
    (hT : ∀ x y, H.Adj x y → x ∈ T) (φ : W' → Finset W)
    (hconn : ∀ x ∈ T, ConnSet G ↑(φ x))
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (φ x) (φ y))
    (hadj : ∀ x y, H.Adj x y → ∃ a ∈ φ x, ∃ b ∈ φ y, G.Adj a b)
    (hG : CliqueMinorFree G k) : CliqueMinorFree H k :=
  fun ⟨M⟩ => hG (nonempty_model_of_transport hk T hT φ hconn hdisj hadj M)

/-- Complete minors are transported along adjacency-preserving injections. -/
theorem cliqueMinorFree_of_embedding (f : W' → W) (hf : Function.Injective f)
    (hadj : ∀ x y, H.Adj x y → G.Adj (f x) (f y)) (hG : CliqueMinorFree G k) :
    CliqueMinorFree H k := by
  classical
  rintro ⟨M⟩
  apply hG
  refine ⟨CliqueMinorModel.ofConnSet (fun i => (M.branch i).image f) (fun i => ?_)
    (fun i j hij => ?_) (fun i j hij => ?_)⟩
  · obtain ⟨x, hx⟩ := (M.connSet i).1
    refine ⟨⟨f x, by simpa using ⟨x, hx, rfl⟩⟩, ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ((M.connSet i).2 a ha b hb).map f (fun x y hxy hx hy => ?_)
    exact RIn.single (hadj x y hxy) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · rw [Finset.disjoint_image hf]
    exact M.branch_disjoint i j hij
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
    exact ⟨f u, Finset.mem_image_of_mem f hu, f v, Finset.mem_image_of_mem f hv, hadj u v huv⟩

end Transport

section Mono

variable {G H : SimpleGraph W} {k : ℕ}

theorem CliqueMinorFree.anti (hG : CliqueMinorFree G k) (hle : H ≤ G) : CliqueMinorFree H k := by
  rintro ⟨M⟩
  exact hG ⟨CliqueMinorModel.ofConnSet M.branch (fun i => (M.connSet i).mono hle)
    M.branch_disjoint (fun i j hij => by
      obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
      exact ⟨u, hu, v, hv, hle huv⟩)⟩

/-- A graph whose edges are all incident to fewer than `k` vertices has no `K_k` minor. -/
theorem cliqueMinorFree_of_edges_subset (hk : 2 ≤ k) (U : Finset W)
    (hU : ∀ a b, H.Adj a b → a ∈ U) (hcard : U.card < k) : CliqueMinorFree H k := by
  classical
  rintro ⟨M⟩
  have hmem := M.mem_of_edges hk (↑U) hU
  have hpick : ∀ i, ∃ x, x ∈ M.branch i := fun i => M.branch_nonempty i
  choose f hf using hpick
  have hinj : Function.Injective (fun i => (⟨f i, hmem i (hf i)⟩ : U)) := by
    intro i j hij
    by_contra hne
    simp only [Subtype.mk.injEq] at hij
    exact Finset.disjoint_left.1 (M.branch_disjoint i j hne) (hf i) (hij ▸ hf j)
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

end Mono

section CliqueSum

variable {H : SimpleGraph W} {k : ℕ}

/-- One half of the clique-sum argument: if every branch set meets `U₁`, intersecting with
`U₁` gives a model in the restriction of `H` to `U₁`. -/
theorem nonempty_model_restrict_of_meets (U₁ U₂ : Set W)
    (hedge : ∀ a b, H.Adj a b → (a ∈ U₁ ∧ b ∈ U₁) ∨ (a ∈ U₂ ∧ b ∈ U₂))
    (hclique : ∀ a ∈ U₁ ∩ U₂, ∀ b ∈ U₁ ∩ U₂, a ≠ b → H.Adj a b)
    (M : CliqueMinorModel H k) (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ U₁) :
    Nonempty (CliqueMinorModel (restrict H U₁) k) := by
  classical
  -- a connected branch set containing a vertex outside `U₁` meets `U₁ ∩ U₂`
  have hZ : ∀ i, ∀ u ∈ M.branch i, u ∉ U₁ → ∃ z ∈ M.branch i, z ∈ U₁ ∩ U₂ := by
    intro i u hu hu1
    obtain ⟨p, hp, hp1⟩ := hmeet i
    obtain ⟨p', q', _, hp's, hp'1, _, hq'1, hpq⟩ :=
      ((M.connSet i).2 p hp u hu).exit (P := U₁) hp1 hu1
    rcases hedge p' q' hpq with h | h
    · exact absurd h.2 hq'1
    · exact ⟨p', hp's, hp'1, h.1⟩
  refine ⟨CliqueMinorModel.ofConnSet (fun i => (M.branch i).filter (· ∈ U₁))
    (fun i => ?_) (fun i j hij => ?_) (fun i j hij => ?_)⟩
  · obtain ⟨x₀, hx₀, hx₀1⟩ := hmeet i
    refine ⟨⟨x₀, by simpa using ⟨hx₀, hx₀1⟩⟩, ?_⟩
    intro p hp q hq
    simp only [Finset.coe_filter] at hp hq
    have key : ∀ r, RIn H ↑(M.branch i) p r → ∃ l, l ∈ M.branch i ∧ l ∈ U₁ ∧
        RIn (restrict H U₁) ↑((M.branch i).filter (· ∈ U₁)) p l ∧ (r ∈ U₁ → l = r) ∧
        (r ∉ U₁ → l ∈ U₂) := by
      intro r hr
      induction hr with
      | refl => exact ⟨p, hp.1, hp.2, RIn.refl _, fun _ => rfl, fun h => absurd hp.2 h⟩
      | @tail c d _ hcd ih =>
        obtain ⟨l, hl, hl1, hpl, hlc, hlc'⟩ := ih
        have hd : d ∈ M.branch i := hcd.2.2
        by_cases hc1 : c ∈ U₁ <;> by_cases hd1 : d ∈ U₁
        · obtain rfl := hlc hc1
          exact ⟨d, hd, hd1, RIn.tail hpl ⟨hcd.1, hc1, hd1⟩ (by simpa using ⟨hl, hl1⟩)
            (by simpa using ⟨hd, hd1⟩),
            fun _ => rfl, fun h => absurd hd1 h⟩
        · obtain rfl := hlc hc1
          refine ⟨l, hl, hl1, hpl, fun h => absurd h hd1, fun _ => ?_⟩
          rcases hedge l d hcd.1 with h | h
          · exact absurd h.2 hd1
          · exact h.1
        · have hl2 := hlc' hc1
          have hd2 : d ∈ U₂ := by
            rcases hedge c d hcd.1 with h | h
            · exact absurd h.1 hc1
            · exact h.2
          refine ⟨d, hd, hd1, ?_, fun _ => rfl, fun h => absurd hd1 h⟩
          by_cases hld : l = d
          · subst hld; exact hpl
          · exact RIn.tail hpl ⟨hclique l ⟨hl1, hl2⟩ d ⟨hd1, hd2⟩ hld, hl1, hd1⟩
              (by simpa using ⟨hl, hl1⟩) (by simpa using ⟨hd, hd1⟩)
        · exact ⟨l, hl, hl1, hpl, fun h => absurd h hd1, fun _ => hlc' hc1⟩
    obtain ⟨l, _, _, hpl, hlq, _⟩ := key q ((M.connSet i).2 p hp.1 q hq.1)
    rw [← hlq hq.2]
    exact hpl
  · exact Finset.disjoint_filter_filter (M.branch_disjoint i j hij)
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
    by_cases h1 : u ∈ U₁ ∧ v ∈ U₁
    · exact ⟨u, by simpa using ⟨hu, h1.1⟩, v, by simpa using ⟨hv, h1.2⟩, huv, h1.1, h1.2⟩
    · have h2 : u ∈ U₂ ∧ v ∈ U₂ := by
        rcases hedge u v huv with h | h
        · exact absurd h h1
        · exact h
      have hzu : ∃ z ∈ M.branch i, z ∈ U₁ ∩ U₂ := by
        by_cases hu1 : u ∈ U₁
        · exact ⟨u, hu, hu1, h2.1⟩
        · exact hZ i u hu hu1
      have hzv : ∃ z ∈ M.branch j, z ∈ U₁ ∩ U₂ := by
        by_cases hv1 : v ∈ U₁
        · exact ⟨v, hv, hv1, h2.2⟩
        · exact hZ j v hv hv1
      obtain ⟨z, hz, hzZ⟩ := hzu
      obtain ⟨z', hz', hz'Z⟩ := hzv
      have hne : z ≠ z' := by
        rintro rfl
        exact Finset.disjoint_left.1 (M.branch_disjoint i j hij) hz hz'
      exact ⟨z, by simpa using ⟨hz, hzZ.1⟩, z', by simpa using ⟨hz', hz'Z.1⟩,
        hclique z hzZ z' hz'Z hne, hzZ.1, hz'Z.1⟩

/-- **Clique-sums.**  If every edge of `H` lies inside `U₁` or inside `U₂`, and
`U₁ ∩ U₂` is a clique of `H`, then a `K_k` minor of `H` (`k ≥ 2`) gives a `K_k` minor of
the restriction of `H` to `U₁` or to `U₂`. -/
theorem cliqueMinorFree_of_cliqueSum (hk : 2 ≤ k) (U₁ U₂ : Set W)
    (hedge : ∀ a b, H.Adj a b → (a ∈ U₁ ∧ b ∈ U₁) ∨ (a ∈ U₂ ∧ b ∈ U₂))
    (hclique : ∀ a ∈ U₁ ∩ U₂, ∀ b ∈ U₁ ∩ U₂, a ≠ b → H.Adj a b)
    (h₁ : CliqueMinorFree (restrict H U₁) k) (h₂ : CliqueMinorFree (restrict H U₂) k) :
    CliqueMinorFree H k := by
  rintro ⟨M⟩
  by_cases hm1 : ∀ i, ∃ x ∈ M.branch i, x ∈ U₁
  · exact h₁ (nonempty_model_restrict_of_meets U₁ U₂ hedge hclique M hm1)
  by_cases hm2 : ∀ i, ∃ x ∈ M.branch i, x ∈ U₂
  · refine h₂ (nonempty_model_restrict_of_meets U₂ U₁ (fun a b h => (hedge a b h).symm)
      (fun a ha b hb hab => hclique a ⟨ha.2, ha.1⟩ b ⟨hb.2, hb.1⟩ hab) M hm2)
  push Not at hm1 hm2
  obtain ⟨i, hi⟩ := hm1
  obtain ⟨j, hj⟩ := hm2
  by_cases hij : i = j
  · subst hij
    obtain ⟨x, hx⟩ := M.branch_nonempty i
    have := M.mem_of_edges hk (U₁ ∪ U₂) (fun a b h => by
      rcases hedge a b h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1) i hx
    rcases this with h | h
    · exact hi x hx h
    · exact hj x hx h
  · obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent i j hij
    rcases hedge u v huv with h | h
    · exact hi u hu h.1
    · exact hj v hv h.2

end CliqueSum

section Apex

variable {V : Type*}

/-- The apex extension `G^{B+α}`: a fresh vertex `none` (the apex `α`) is added to `G`
(whose vertices are embedded as `some v`), adjacent exactly to the vertices of `B`. -/
def apexExtend (G : SimpleGraph V) (B : Set V) : SimpleGraph (Option V) where
  Adj
    | some a, some b => G.Adj a b
    | none, some b => b ∈ B
    | some a, none => a ∈ B
    | none, none => False
  symm := ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact G.irrefl h⟩

@[simp] theorem apexExtend_some_some {G : SimpleGraph V} {B : Set V} {a b : V} :
    (apexExtend G B).Adj (some a) (some b) ↔ G.Adj a b := Iff.rfl

@[simp] theorem apexExtend_none_some {G : SimpleGraph V} {B : Set V} {b : V} :
    (apexExtend G B).Adj none (some b) ↔ b ∈ B := Iff.rfl

@[simp] theorem apexExtend_some_none {G : SimpleGraph V} {B : Set V} {a : V} :
    (apexExtend G B).Adj (some a) none ↔ a ∈ B := Iff.rfl

@[simp] theorem apexExtend_none_none {G : SimpleGraph V} {B : Set V} :
    ¬ (apexExtend G B).Adj none none := id

theorem apexExtend_mono {G G' : SimpleGraph V} {B B' : Set V} (hG : G ≤ G') (hB : B ⊆ B') :
    apexExtend G B ≤ apexExtend G' B' := by
  rintro (_ | a) (_ | b) h
  · exact h
  · exact hB h
  · exact hB h
  · exact hG h

/-- `G` has no `K_5` minor. -/
def K5MinorFree (G : SimpleGraph V) : Prop := CliqueMinorFree G 5

/-- `B` is a `K_5`-minor-free boundary of `G` (Wood--Linusson, Definition 2): the apex
extension `G^{B+α}` has no `K_5` minor. -/
def IsK5Boundary (G : SimpleGraph V) (B : Set V) : Prop := K5MinorFree (apexExtend G B)

theorem k5MinorFree_of_isK5Boundary {G : SimpleGraph V} {B : Set V} (h : IsK5Boundary G B) :
    K5MinorFree G := by
  classical
  exact cliqueMinorFree_of_embedding some (Option.some_injective V)
    (fun x y hxy => by simpa using hxy) h

theorem isK5Boundary_empty_iff {G : SimpleGraph V} : IsK5Boundary G ∅ ↔ K5MinorFree G := by
  classical
  refine ⟨k5MinorFree_of_isK5Boundary, fun h => ?_⟩
  refine cliqueMinorFree_of_transport (by norm_num) (Set.range some) ?_
    (fun x => x.elim ∅ ({·})) ?_ ?_ ?_ h
  · rintro (_ | a) (_ | b) hab
    · exact absurd hab id
    · simp at hab
    · exact ⟨a, rfl⟩
    · exact ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    simpa using connSet_singleton G a
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    simpa using fun h => hab (congrArg some h)
  · rintro (_ | a) (_ | b) hab
    · exact absurd hab id
    · simp at hab
    · simp at hab
    · exact ⟨a, by simp, b, by simp, hab⟩

end Apex

end LeanPool.K5MinorFreeChoosability
