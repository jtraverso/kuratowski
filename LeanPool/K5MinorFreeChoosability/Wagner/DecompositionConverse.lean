/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Decomposition

/-!
# The easy direction: decomposable graphs are `K_{3,3}`-minor-free

Gluing two `K_{3,3}`-minor-free induced pieces along a retained clique of order at most two
gives a `K_{3,3}`-minor-free graph (`k33MinorFree_restrict_union`); hence every graph with a
`K33Decomp` certificate is `K_{3,3}`-minor-free (`k33MinorFree_of_k33Decomp`).  Together with
`exists_k33Decomp` this characterises finite `K_{3,3}`-minor-free graphs as the spanning
subgraphs of graphs with a `K33Decomp` certificate (`k33MinorFree_iff_exists_k33Decomp`).

Proof of the gluing step: at most two branch sets of a `K_{3,3}` model meet the separator
`K = A ∩ B`; the others are connected sets avoiding `K`, hence lie in `A \ B` or in `B \ A`,
and since `K_{3,3}` minus two vertices is connected they all lie on the same side, say `A`.
Intersecting every branch set with `A` gives a `K_{3,3}` model in `H[A]` (using the clique
edge on `K` to reconnect and to replace adjacencies through `B \ A`).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem rIn_restrict_of_sub {H : SimpleGraph V} {T A : Set V} {s : Set V} (hs : s ⊆ A)
    {a b : V} (h : RIn (restrict H T) s a b) : RIn (restrict H A) s a b := by
  induction h with
  | refl => exact RIn.refl _
  | tail _ hcd ih => exact ih.tail ⟨hcd.1.1, hs hcd.2.1, hs hcd.2.2⟩ hcd.2.1 hcd.2.2

/-- Projection of a `K_{3,3}` model onto the side `A` of a retained-clique gluing, when all
branch sets missing the separator lie in `A`. -/
theorem isMinor_K33_project {H : SimpleGraph V} {A B : Finset V}
    (hcl : ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → H.Adj u v)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v)
    {T : Finset V} (hT : T = A ∪ B) (Mo : MinorModel (restrict H ↑T) K33)
    (hside : ∀ w, (∀ k ∈ Mo.branch w, k ∉ A ∩ B) → Mo.branch w ⊆ A) :
    IsMinor K33 (restrict H ↑A) := by
  classical
  have hmemAB : ∀ w, ∀ x ∈ Mo.branch w, x ∈ A ∪ B := fun w x hx => by
    have := Mo.mem_of_edges K33_hasNeighbor (↑T) (fun x y h => h.2.1) w hx
    rw [← hT]; exact_mod_cast this
  -- the projected branch sets
  let Y : Fin 3 ⊕ Fin 3 → Finset V := fun w => Mo.branch w ∩ A
  have hYsub : ∀ w, Y w ⊆ Mo.branch w := fun w => Finset.inter_subset_left
  have hYA : ∀ w, Y w ⊆ A := fun w => Finset.inter_subset_right
  -- a vertex of `B \ A` in a branch set forces the branch set to meet the separator
  have hmeet : ∀ w, ∀ u ∈ Mo.branch w, u ∉ A → ∃ k ∈ Mo.branch w, k ∈ A ∩ B := by
    intro w u hu huA
    by_contra h
    push Not at h
    exact huA (hside w h hu)
  have hconn : ∀ w, ConnSet (restrict H ↑A) ↑(Y w) := by
    intro w
    by_cases hw : ∃ k ∈ Mo.branch w, k ∈ A ∩ B
    · obtain ⟨k₀, hk₀, hk₀K⟩ := hw
      have hk₀Y : k₀ ∈ Y w := Finset.mem_inter.2 ⟨hk₀, (Finset.mem_inter.1 hk₀K).1⟩
      have key : ∀ a ∈ Y w, RIn (restrict H ↑A) ↑(Y w) a k₀ := by
        intro a ha
        obtain ⟨haX, haA⟩ := Finset.mem_inter.1 ha
        -- from a separator vertex `q` of the branch set to `k₀`
        have toK : ∀ q ∈ Mo.branch w, q ∈ A ∩ B → RIn (restrict H ↑A) ↑(Y w) q k₀ := by
          intro q hq hqK
          by_cases hqk : q = k₀
          · subst hqk; exact RIn.refl _
          · have hqY : q ∈ Y w := Finset.mem_inter.2 ⟨hq, (Finset.mem_inter.1 hqK).1⟩
            exact RIn.single ⟨hcl q hqK k₀ hk₀K hqk, (Finset.mem_inter.1 hqK).1,
              (Finset.mem_inter.1 hk₀K).1⟩ (by exact_mod_cast hqY) (by exact_mod_cast hk₀Y)
        by_cases haB : a ∈ B
        · exact toK a haX (Finset.mem_inter.2 ⟨haA, haB⟩)
        · have hr := (Mo.connSet w).2 a haX k₀ hk₀
          obtain ⟨p, q, hap, hpX, hpP, hqX, hqP, hpq⟩ := hr.exit (P := ↑(A \ B))
            (by simp [haA, haB]) (by simp [(Finset.mem_inter.1 hk₀K).2])
          have hpAB : p ∈ A \ B := by exact_mod_cast hpP
          have hqAB : q ∈ A ∪ B := hmemAB w q (by exact_mod_cast hqX)
          have hqK : q ∈ A ∩ B := by
            have hqA : q ∈ A := by
              by_contra hqA
              have hqB : q ∈ B := (Finset.mem_union.1 hqAB).resolve_left hqA
              exact hnc p (Finset.mem_sdiff.1 hpAB).1 (Finset.mem_sdiff.1 hpAB).2 q hqB hqA hpq.1
            refine Finset.mem_inter.2 ⟨hqA, ?_⟩
            by_contra hqB
            exact hqP (by simp [hqA, hqB])
          have hsub : (↑(Mo.branch w) : Set V) ∩ ↑(A \ B) ⊆ ↑(Y w) := by
            intro x ⟨hx1, hx2⟩
            have hx2' : x ∈ A \ B := by exact_mod_cast hx2
            exact_mod_cast Finset.mem_inter.2 ⟨by exact_mod_cast hx1, (Finset.mem_sdiff.1 hx2').1⟩
          have hpY : p ∈ Y w := Finset.mem_inter.2 ⟨by exact_mod_cast hpX,
            (Finset.mem_sdiff.1 hpAB).1⟩
          have hqY : q ∈ Y w := Finset.mem_inter.2 ⟨by exact_mod_cast hqX,
            (Finset.mem_inter.1 hqK).1⟩
          have h1 : RIn (restrict H ↑A) ↑(Y w) a p :=
            rIn_restrict_of_sub (fun x hx => by exact_mod_cast hYA w (by exact_mod_cast hx))
              (hap.mono_set hsub)
          exact (h1.tail ⟨hpq.1, by exact_mod_cast (Finset.mem_sdiff.1 hpAB).1,
            by exact_mod_cast (Finset.mem_inter.1 hqK).1⟩ (by exact_mod_cast hpY)
            (by exact_mod_cast hqY)).trans (toK q (by exact_mod_cast hqX) hqK)
      exact ⟨⟨k₀, by exact_mod_cast hk₀Y⟩, fun a ha b hb =>
        (key a (by exact_mod_cast ha)).trans (key b (by exact_mod_cast hb)).symm⟩
    · push Not at hw
      have hXA := hside w hw
      have hYeq : Y w = Mo.branch w := Finset.inter_eq_left.2 hXA
      rw [hYeq]
      have hc := Mo.connSet w
      exact ⟨hc.1, fun a ha b hb =>
        rIn_restrict_of_sub (fun x hx => by exact_mod_cast hXA (by exact_mod_cast hx))
          (hc.2 a ha b hb)⟩
  refine isMinor_K33_of_sets Y hconn (fun w w' hww' => (Mo.branch_disjoint w w' hww').mono
    (hYsub w) (hYsub w')) (fun i j => ?_)
  obtain ⟨u, hu, v, hv, huv⟩ := Mo.branch_adjacent (Sum.inl i) (Sum.inr j) (by simp)
  have hne : (Sum.inl i : Fin 3 ⊕ Fin 3) ≠ Sum.inr j := by simp
  by_cases huA : u ∈ A
  · by_cases hvA : v ∈ A
    · exact ⟨u, Finset.mem_inter.2 ⟨hu, huA⟩, v, Finset.mem_inter.2 ⟨hv, hvA⟩,
        huv.1, huA, hvA⟩
    · -- `v ∈ B \ A`, so `u ∈ B` and both branch sets meet the separator
      have hvB : v ∈ B := (Finset.mem_union.1 (hmemAB _ v hv)).resolve_left hvA
      have huB : u ∈ B := by
        by_contra huB
        exact hnc u huA huB v hvB hvA huv.1
      obtain ⟨k', hk', hk'K⟩ := hmeet _ v hv hvA
      have hk'u : u ≠ k' := fun h => Finset.disjoint_left.1 (Mo.branch_disjoint _ _ hne) hu
        (h ▸ hk')
      exact ⟨u, Finset.mem_inter.2 ⟨hu, huA⟩, k', Finset.mem_inter.2 ⟨hk',
        (Finset.mem_inter.1 hk'K).1⟩, hcl u (Finset.mem_inter.2 ⟨huA, huB⟩) k' hk'K hk'u,
        huA, (Finset.mem_inter.1 hk'K).1⟩
  · have huB : u ∈ B := (Finset.mem_union.1 (hmemAB _ u hu)).resolve_left huA
    have hvB : v ∈ B := by
      by_contra hvB
      have hvA : v ∈ A := (Finset.mem_union.1 (hmemAB _ v hv)).resolve_right hvB
      exact hnc v hvA hvB u huB huA huv.1.symm
    obtain ⟨k, hk, hkK⟩ := hmeet _ u hu huA
    obtain ⟨k', hk', hk'K⟩ : ∃ k' ∈ Mo.branch (Sum.inr j), k' ∈ A ∩ B := by
      by_cases hvA : v ∈ A
      · exact ⟨v, hv, Finset.mem_inter.2 ⟨hvA, hvB⟩⟩
      · exact hmeet _ v hv hvA
    have hkk' : k ≠ k' := fun h => Finset.disjoint_left.1 (Mo.branch_disjoint _ _ hne) hk
      (h ▸ hk')
    exact ⟨k, Finset.mem_inter.2 ⟨hk, (Finset.mem_inter.1 hkK).1⟩, k',
      Finset.mem_inter.2 ⟨hk', (Finset.mem_inter.1 hk'K).1⟩, hcl k hkK k' hk'K hkk',
      (Finset.mem_inter.1 hkK).1, (Finset.mem_inter.1 hk'K).1⟩

/-- **Gluing along a retained clique of order at most two preserves `K_{3,3}`-minor-freeness.** -/
theorem k33MinorFree_restrict_union {H : SimpleGraph V} {A B : Finset V}
    (hcard : (A ∩ B).card ≤ 2) (hcl : ∀ u ∈ A ∩ B, ∀ v ∈ A ∩ B, u ≠ v → H.Adj u v)
    (hnc : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ H.Adj u v)
    (hA : K33MinorFree (restrict H ↑A)) (hB : K33MinorFree (restrict H ↑B)) :
    K33MinorFree (restrict H ↑(A ∪ B)) := by
  classical
  rintro ⟨Mo⟩
  have hmemAB : ∀ w, ∀ x ∈ Mo.branch w, x ∈ A ∪ B := fun w x hx => by
    have := Mo.mem_of_edges K33_hasNeighbor (↑(A ∪ B)) (fun x y h => h.2.1) w hx
    exact_mod_cast this
  let MK : Fin 3 ⊕ Fin 3 → Prop := fun w => ∃ k ∈ Mo.branch w, k ∈ A ∩ B
  -- at most two branch sets meet the separator
  have hthree : ∀ w₁ w₂ w₃, w₁ ≠ w₂ → w₁ ≠ w₃ → w₂ ≠ w₃ → MK w₁ → MK w₂ → MK w₃ → False := by
    rintro w₁ w₂ w₃ h12 h13 h23 ⟨k₁, hk₁, hK₁⟩ ⟨k₂, hk₂, hK₂⟩ ⟨k₃, hk₃, hK₃⟩
    have hd : ∀ {w w' : Fin 3 ⊕ Fin 3} {k k' : V}, w ≠ w' → k ∈ Mo.branch w →
        k' ∈ Mo.branch w' → k ≠ k' := fun h hk hk' he =>
      Finset.disjoint_left.1 (Mo.branch_disjoint _ _ h) hk (he ▸ hk')
    have hsub : ({k₁, k₂, k₃} : Finset V) ⊆ A ∩ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hd h12 hk₁ hk₂, hd h13 hk₁ hk₃]),
      Finset.card_pair (hd h23 hk₂ hk₃)] at hc
    omega
  -- branch sets missing the separator lie on one side
  have hpure : ∀ w, ¬ MK w → Mo.branch w ⊆ A \ B ∨ Mo.branch w ⊆ B \ A := by
    intro w hw
    simp only [MK, not_exists, not_and] at hw
    obtain ⟨x₀, hx₀⟩ := Mo.branch_nonempty w
    have hx₀K : x₀ ∉ A ∩ B := hw x₀ hx₀
    have side : ∀ P Q : Finset V, (∀ u ∈ P, u ∉ Q → ∀ v ∈ Q, v ∉ P → ¬ H.Adj u v) →
        x₀ ∈ P → x₀ ∉ Q → (∀ x ∈ Mo.branch w, x ∈ P ∪ Q) →
        (∀ x ∈ Mo.branch w, ¬ (x ∈ P ∧ x ∈ Q)) → Mo.branch w ⊆ P \ Q := by
      intro P Q hPQ hx₀P hx₀Q hcov hnot x hx
      have hr := (Mo.connSet w).2 x₀ hx₀ x hx
      induction hr with
      | refl => exact Finset.mem_sdiff.2 ⟨hx₀P, hx₀Q⟩
      | @tail p q _ hpq ih =>
        have hpX : p ∈ Mo.branch w := by exact_mod_cast hpq.2.1
        have hqX : q ∈ Mo.branch w := by exact_mod_cast hpq.2.2
        obtain ⟨hpP, hpQ⟩ := Finset.mem_sdiff.1 (ih hpX)
        have hqPQ := hcov q hqX
        by_cases hqP : q ∈ P
        · exact Finset.mem_sdiff.2 ⟨hqP, fun hqQ => hnot q hqX ⟨hqP, hqQ⟩⟩
        · exact absurd hpq.1.1 (hPQ p hpP hpQ q ((Finset.mem_union.1 hqPQ).resolve_left hqP) hqP)
    have hnotK : ∀ x ∈ Mo.branch w, ¬ (x ∈ A ∧ x ∈ B) := fun x hx h =>
      hw x hx (Finset.mem_inter.2 h)
    by_cases hx₀A : x₀ ∈ A
    · have hx₀B : x₀ ∉ B := fun h => hx₀K (Finset.mem_inter.2 ⟨hx₀A, h⟩)
      exact Or.inl (side A B hnc hx₀A hx₀B (hmemAB w) hnotK)
    · have hx₀B : x₀ ∈ B := (Finset.mem_union.1 (hmemAB w x₀ hx₀)).resolve_left hx₀A
      refine Or.inr (side B A (fun u hu huA v hv hvB huv => hnc v hv hvB u hu huA huv.symm)
        hx₀B hx₀A (fun x hx => by rw [Finset.union_comm]; exact hmemAB w x hx)
        (fun x hx h => hnotK x hx ⟨h.2, h.1⟩))
  -- adjacent branch sets missing the separator lie on the same side
  have hsame : ∀ w w', ¬ MK w → ¬ MK w' → K33.Adj w w' → Mo.branch w ⊆ A \ B →
      Mo.branch w' ⊆ A \ B := by
    intro w w' hw hw' hadj hwA
    rcases hpure w' hw' with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu, v, hv, huv⟩ := Mo.branch_adjacent w w' hadj
      exact hnc u (Finset.mem_sdiff.1 (hwA hu)).1 (Finset.mem_sdiff.1 (hwA hu)).2 v
        (Finset.mem_sdiff.1 (h hv)).1 (Finset.mem_sdiff.1 (h hv)).2 huv.1
  have hsame' : ∀ w w', ¬ MK w → ¬ MK w' → K33.Adj w w' → Mo.branch w ⊆ B \ A →
      Mo.branch w' ⊆ B \ A := by
    intro w w' hw hw' hadj hwB
    rcases hpure w' hw' with h | h
    · exfalso
      obtain ⟨u, hu, v, hv, huv⟩ := Mo.branch_adjacent w w' hadj
      exact hnc v (Finset.mem_sdiff.1 (h hv)).1 (Finset.mem_sdiff.1 (h hv)).2 u
        (Finset.mem_sdiff.1 (hwB hu)).1 (Finset.mem_sdiff.1 (hwB hu)).2 huv.1.symm
    · exact h
  -- any two vertices of `K_{3,3}` outside the separator-meeting ones are joined by a path of
  -- length at most two avoiding them
  have hpath : ∀ w w', ¬ MK w → ¬ MK w' → w = w' ∨ K33.Adj w w' ∨
      ∃ w'', ¬ MK w'' ∧ K33.Adj w w'' ∧ K33.Adj w'' w' := by
    intro w w' hw hw'
    rcases w with i | i <;> rcases w' with j | j
    · by_cases hij : i = j
      · exact Or.inl (by rw [hij])
      · right; right
        by_contra hno
        push Not at hno
        have h0 : MK (Sum.inr 0) := by
          by_contra h; exact hno _ h (by simp) (by simp)
        have h1 : MK (Sum.inr 1) := by
          by_contra h; exact hno _ h (by simp) (by simp)
        have h2 : MK (Sum.inr 2) := by
          by_contra h; exact hno _ h (by simp) (by simp)
        exact hthree _ _ _ (by decide) (by decide) (by decide) h0 h1 h2
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inl (by simp))
    · by_cases hij : i = j
      · exact Or.inl (by rw [hij])
      · right; right
        by_contra hno
        push Not at hno
        have h0 : MK (Sum.inl 0) := by
          by_contra h; exact hno _ h (by simp) (by simp)
        have h1 : MK (Sum.inl 1) := by
          by_contra h; exact hno _ h (by simp) (by simp)
        have h2 : MK (Sum.inl 2) := by
          by_contra h; exact hno _ h (by simp) (by simp)
        exact hthree _ _ _ (by decide) (by decide) (by decide) h0 h1 h2
  -- a branch set missing the separator
  obtain ⟨w₀, hw₀⟩ : ∃ w, ¬ MK w := by
    by_contra h
    push Not at h
    exact hthree (Sum.inl 0) (Sum.inl 1) (Sum.inl 2) (by decide) (by decide) (by decide)
      (h _) (h _) (h _)
  rcases hpure w₀ hw₀ with h₀ | h₀
  · refine hA (isMinor_K33_project hcl hnc rfl Mo fun w hw => ?_)
    have hw' : ¬ MK w := fun ⟨k, hk, hkK⟩ => hw k hk hkK
    have : Mo.branch w ⊆ A \ B := by
      rcases hpath w₀ w hw₀ hw' with rfl | hadj | ⟨w'', hw'', h1, h2⟩
      · exact h₀
      · exact hsame _ _ hw₀ hw' hadj h₀
      · exact hsame _ _ hw'' hw' h2 (hsame _ _ hw₀ hw'' h1 h₀)
    exact this.trans Finset.sdiff_subset
  · have hcl' : ∀ u ∈ B ∩ A, ∀ v ∈ B ∩ A, u ≠ v → H.Adj u v := by
      rw [Finset.inter_comm]; exact hcl
    have hnc' : ∀ u ∈ B, u ∉ A → ∀ v ∈ A, v ∉ B → ¬ H.Adj u v :=
      fun u hu huA v hv hvB huv => hnc v hv hvB u hu huA huv.symm
    refine hB (isMinor_K33_project hcl' hnc' (Finset.union_comm A B) Mo fun w hw => ?_)
    have hw' : ¬ MK w := fun ⟨k, hk, hkK⟩ => hw k hk (by rwa [Finset.inter_comm])
    have : Mo.branch w ⊆ B \ A := by
      rcases hpath w₀ w hw₀ hw' with rfl | hadj | ⟨w'', hw'', h1, h2⟩
      · exact h₀
      · exact hsame' _ _ hw₀ hw' hadj h₀
      · exact hsame' _ _ hw'' hw' h2 (hsame' _ _ hw₀ hw'' h1 h₀)
    exact this.trans Finset.sdiff_subset

/-- Every graph with a `K33Decomp` certificate on `S` is `K_{3,3}`-minor-free on `S`. -/
theorem k33MinorFree_of_k33Decomp {H : SimpleGraph V} {S : Finset V} (hd : K33Decomp H S) :
    K33MinorFree (restrict H ↑S) := by
  induction hd with
  | small _ h => exact h
  | prime _ h _ => exact h
  | glue _ _ hcard hcl hnc _ _ ihA ihB => exact k33MinorFree_restrict_union hcard hcl hnc ihA ihB

/-- **Characterisation of finite `K_{3,3}`-minor-free graphs.**  A finite graph has no
`K_{3,3}` minor if and only if it is a spanning subgraph of a graph with a `K33Decomp`
certificate (retained-clique gluings of order `≤ 2` of pieces that are small or prime). -/
theorem k33MinorFree_iff_exists_k33Decomp [Fintype V] (G : SimpleGraph V) :
    K33MinorFree G ↔ ∃ H : SimpleGraph V, G ≤ H ∧ K33Decomp H Finset.univ := by
  constructor
  · exact exists_k33Decomp G
  · rintro ⟨H, hGH, hd⟩ hG
    have h := k33MinorFree_of_k33Decomp hd
    have he : restrict H ↑(Finset.univ : Finset V) = H := by
      ext u v; simp [restrict_adj]
    rw [he] at h
    exact h (hG.mono hGH)

end LeanPool.K5MinorFreeChoosability
