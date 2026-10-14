/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Kuratowski.Defs

/-!
# Joining terminals inside a connected vertex set

* `exists_centre_three`: at most three terminals in a connected vertex set `B` can be joined to a
  common centre by paths inside `B` that pairwise meet only at the centre (terminals may repeat).
* `exists_centre_four`: four terminals in a connected vertex set `B` can be joined to two centres
  `c` and `d` (possibly equal) inside `B`; if `c ≠ d`, each centre serves exactly two terminals
  and there is a `c`–`d` path inside `B`; all paths meet only where forced.

Proof idea: for three terminals, take a path `P` from `a₁` to `a₂` inside `B` and a shortest path
`Q` from `a₃` to `P` inside `B`, hitting `P` first at `c`; split `P` at `c`. For four terminals,
take a shortest path from `a₄` to the union of the three paths, hitting it first at `x`: if
`x = c` this is a star; otherwise `x` lies on the path to some `aᵢ` and `x` becomes the second
centre, serving `aᵢ` and `a₄`.
-/

@[expose] public section

open SimpleGraph

namespace Kuratowski

variable {V : Type*}

private theorem walk_first_hit {G : SimpleGraph V} (S : Set V) :
    ∀ {u s : V} (w : G.Walk u s), s ∈ S → ∃ x ∈ S, ∃ q : G.Walk u x,
      q.support ⊆ w.support ∧ ∀ v ∈ q.support, v ∈ S → v = x := by
  intro u s w
  induction w with
  | nil => intro hs; exact ⟨_, hs, Walk.nil, by simp, by simp⟩
  | @cons u u' s h w ih =>
    intro hs
    by_cases hu : u ∈ S
    · exact ⟨u, hu, Walk.nil, by simp, by simp⟩
    · obtain ⟨x, hx, q, hsub, hq⟩ := ih hs
      refine ⟨x, hx, Walk.cons h q, ?_, ?_⟩
      · simp only [Walk.support_cons]
        exact List.cons_subset_cons _ hsub
      · intro v hv hvS
        rw [Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact absurd hvS hu
        · exact hq v hv hvS

private theorem walk_in_set {G : SimpleGraph V} {B : Set V} (hB : (G.induce B).Connected) {u v : V}
    (hu : u ∈ B) (hv : v ∈ B) : ∃ w : G.Walk u v, ∀ x ∈ w.support, x ∈ B := by
  obtain ⟨w⟩ := hB.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  have key : ∀ x ∈ (w.map (Embedding.induce B).toHom).support, x ∈ B := by
    intro x hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  exact ⟨w.map (Embedding.induce B).toHom, key⟩

private theorem path_first_hit {G : SimpleGraph V} {B : Set V} (hB : (G.induce B).Connected) {u : V}
    (hu : u ∈ B) (S : Set V) {s : V} (hs : s ∈ S) (hsB : s ∈ B) :
    ∃ x ∈ S, ∃ q : G.Walk u x, q.IsPath ∧ (∀ v ∈ q.support, v ∈ B) ∧
      ∀ v ∈ q.support, v ∈ S → v = x := by
  classical
  obtain ⟨w, hw⟩ := walk_in_set hB hu hsB
  obtain ⟨x, hx, q, hsub, hq⟩ := walk_first_hit S w hs
  refine ⟨x, hx, q.bypass, q.bypass_isPath,
    fun v hv => hw v (hsub (q.support_bypass_subset_support hv)),
    fun v hv => hq v (q.support_bypass_subset_support hv)⟩

private theorem append_path_meet {G : SimpleGraph V} {u c w : V} (p : G.Walk u c) (q : G.Walk c w)
    (h : (p.append q).IsPath) {v : V} (hp : v ∈ p.support) (hq : v ∈ q.support) : v = c := by
  have nd := h.support_nodup
  rw [Walk.support_append] at nd
  rw [← Walk.cons_tail_support q, List.mem_cons] at hq
  rcases hq with h' | h'
  · exact h'
  · exact absurd h' (List.disjoint_of_nodup_append nd hp)

private theorem centre_three_core {G : SimpleGraph V} {B : Set V}
    (hB : (G.induce B).Connected) {a₁ a₂ a₃ : V} (h₁ : a₁ ∈ B) (h₂ : a₂ ∈ B) (h₃ : a₃ ∈ B) :
    ∃ c ∈ B, ∃ p₁ : G.Walk c a₁, ∃ p₂ : G.Walk c a₂, ∃ p₃ : G.Walk c a₃,
      p₁.IsPath ∧ p₂.IsPath ∧ p₃.IsPath ∧
      (∀ v ∈ p₁.support, v ∈ B) ∧ (∀ v ∈ p₂.support, v ∈ B) ∧ (∀ v ∈ p₃.support, v ∈ B) ∧
      (∀ v ∈ p₁.support, v ∈ p₂.support → v = c) ∧
      (∀ v ∈ p₁.support, v ∈ p₃.support → v = c) ∧
      (∀ v ∈ p₂.support, v ∈ p₃.support → v = c) := by
  classical
  obtain ⟨w, hw⟩ := walk_in_set hB h₁ h₂
  set P := w.bypass with hPdef
  have hP : P.IsPath := w.bypass_isPath
  have hPB : ∀ v ∈ P.support, v ∈ B := fun v hv => hw v (w.support_bypass_subset_support hv)
  obtain ⟨c, hc, Q, hQ, hQB, hQS⟩ :=
    path_first_hit hB h₃ {v | v ∈ P.support} (s := a₁) P.start_mem_support h₁
  have hcB : c ∈ B := hPB c hc
  have hT : ∀ v ∈ (P.takeUntil c hc).support, v ∈ P.support :=
    fun v hv => P.support_takeUntil_subset_support hc hv
  have hD : ∀ v ∈ (P.dropUntil c hc).support, v ∈ P.support :=
    fun v hv => P.support_dropUntil_subset_support hc hv
  refine ⟨c, hcB, (P.takeUntil c hc).reverse, P.dropUntil c hc, Q.reverse,
    (hP.takeUntil hc).reverse, hP.dropUntil hc, hQ.reverse, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; rw [Walk.support_reverse, List.mem_reverse] at hv; exact hPB v (hT v hv)
  · intro v hv; exact hPB v (hD v hv)
  · intro v hv; rw [Walk.support_reverse, List.mem_reverse] at hv; exact hQB v hv
  · intro v hv1 hv2
    rw [Walk.support_reverse, List.mem_reverse] at hv1
    have hPP : ((P.takeUntil c hc).append (P.dropUntil c hc)).IsPath := by
      rw [Walk.take_spec]; exact hP
    exact append_path_meet _ _ hPP hv1 hv2
  · intro v hv1 hv2
    rw [Walk.support_reverse, List.mem_reverse] at hv1 hv2
    exact hQS v hv2 (hT v hv1)
  · intro v hv1 hv2
    rw [Walk.support_reverse, List.mem_reverse] at hv2
    exact hQS v hv2 (hD v hv1)


/-- **Three terminals.** Terminals (at most three, possibly repeated) in a connected vertex set
`B` are joined to a common centre by paths inside `B` that pairwise meet only at the centre. -/
theorem exists_centre_three {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 3)
    {G : SimpleGraph V} {B : Set V} (hB : (G.induce B).Connected) (a : ι → V)
    (ha : ∀ i, a i ∈ B) :
    ∃ c ∈ B, ∃ p : ∀ i, G.Walk c (a i), (∀ i, (p i).IsPath) ∧
      (∀ i, ∀ v ∈ (p i).support, v ∈ B) ∧
      ∀ i j, i ≠ j → ∀ v ∈ (p i).support, v ∈ (p j).support → v = c := by
  classical
  rcases isEmpty_or_nonempty ι with hι0 | hι0
  · obtain ⟨⟨c, hc⟩⟩ := hB.nonempty
    exact ⟨c, hc, fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i,
      fun i => isEmptyElim i⟩
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin 3) := Function.Embedding.nonempty_of_card_le (by simpa using hι)
  have hge : ∀ i, Function.invFun e (e i) = i := fun i => Function.leftInverse_invFun e.injective i
  obtain ⟨c, hc, p₁, p₂, p₃, hp₁, hp₂, hp₃, hB₁, hB₂, hB₃, h₁₂, h₁₃, h₂₃⟩ :=
    centre_three_core hB (ha (Function.invFun e 0)) (ha (Function.invFun e 1))
      (ha (Function.invFun e 2))
  have h2 : ∀ i, e i ≠ 0 → e i ≠ 1 → e i = 2 := by
    intro i h0 h1
    generalize e i = k at h0 h1 ⊢
    revert k; decide
  let p : ∀ i, G.Walk c (a i) := fun i =>
    if h0 : e i = 0 then p₁.copy rfl (by rw [← h0, hge i])
    else if h1 : e i = 1 then p₂.copy rfl (by rw [← h1, hge i])
    else p₃.copy rfl (by rw [← h2 i h0 h1, hge i])
  have key : ∀ i, ((p i).IsPath ∧ ∀ v ∈ (p i).support, v ∈ B) ∧
      ((e i = 0 ∧ (p i).support = p₁.support) ∨ (e i = 1 ∧ (p i).support = p₂.support) ∨
        (e i = 2 ∧ (p i).support = p₃.support)) := by
    intro i
    simp only [p]
    split_ifs with h0 h1
    · exact ⟨⟨by simpa using hp₁, by rw [Walk.support_copy]; exact hB₁⟩,
        Or.inl ⟨h0, Walk.support_copy _ _ _⟩⟩
    · exact ⟨⟨by simpa using hp₂, by rw [Walk.support_copy]; exact hB₂⟩,
        Or.inr (Or.inl ⟨h1, Walk.support_copy _ _ _⟩)⟩
    · exact ⟨⟨by simpa using hp₃, by rw [Walk.support_copy]; exact hB₃⟩,
        Or.inr (Or.inr ⟨h2 i h0 h1, Walk.support_copy _ _ _⟩)⟩
  refine ⟨c, hc, p, fun i => (key i).1.1, fun i => (key i).1.2, ?_⟩
  intro i j hij v hvi hvj
  have hne : e i ≠ e j := e.injective.ne hij
  rcases (key i).2 with ⟨hi, hs⟩ | ⟨hi, hs⟩ | ⟨hi, hs⟩ <;>
    rcases (key j).2 with ⟨hj, hs'⟩ | ⟨hj, hs'⟩ | ⟨hj, hs'⟩ <;>
    rw [hs] at hvi <;> rw [hs'] at hvj <;>
    first
    | exact absurd (hi.trans hj.symm) hne
    | exact h₁₂ v hvi hvj | exact h₁₂ v hvj hvi
    | exact h₁₃ v hvi hvj | exact h₁₃ v hvj hvi
    | exact h₂₃ v hvi hvj | exact h₂₃ v hvj hvi

/-- **Four terminals.** Four terminals (possibly repeated) in a connected vertex set `B` are joined
inside `B` to centres `ctr i ∈ {c, d}` by paths `p i`, together with a `c`–`d` path `r`:
* either `c = d` (a star; `r` is then irrelevant), or `c ≠ d`, each centre serves exactly two
  terminals;
* two terminal paths meet only at a common centre;
* a terminal path meets `r` only at its own centre. -/
theorem exists_centre_four [DecidableEq V] {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 4)
    {G : SimpleGraph V} {B : Set V} (hB : (G.induce B).Connected) (a : ι → V)
    (ha : ∀ i, a i ∈ B) :
    ∃ c ∈ B, ∃ d ∈ B, ∃ r : G.Walk c d, ∃ ctr : ι → V, ∃ p : ∀ i, G.Walk (ctr i) (a i),
      r.IsPath ∧ (∀ v ∈ r.support, v ∈ B) ∧
      (∀ i, ctr i = c ∨ ctr i = d) ∧
      (c ≠ d → (Finset.univ.filter fun i => ctr i = c).card = 2) ∧
      (∀ i, (p i).IsPath) ∧ (∀ i, ∀ v ∈ (p i).support, v ∈ B) ∧
      (∀ i j, i ≠ j → ∀ v ∈ (p i).support, v ∈ (p j).support → v = ctr i ∧ ctr i = ctr j) ∧
      (c ≠ d → ∀ i, ∀ v ∈ (p i).support, v ∈ r.support → v = ctr i) := by
  classical
  obtain ⟨i₄⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card ι by omega)
  have hcard : Fintype.card {i // i ≠ i₄} = 3 := by
    rw [Fintype.card_subtype_compl, hι, Fintype.card_subtype_eq]
  obtain ⟨c, hc, q, hqP, hqB, hqD⟩ :=
    exists_centre_three (ι := {i // i ≠ i₄}) hcard.le hB (fun i => a i.1) (fun i => ha i.1)
  obtain ⟨j₀⟩ : Nonempty {i // i ≠ i₄} := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x, ⟨m, hxm⟩, R, hR, hRB, hRS⟩ :=
    path_first_hit hB (ha i₄) {v | ∃ k, v ∈ (q k).support} (s := c)
      ⟨j₀, (q j₀).start_mem_support⟩ hc
  by_cases hxc : x = c
  · subst hxc
    refine ⟨x, hc, x, hc, Walk.nil, fun _ => x,
      fun i => if h : i = i₄ then R.reverse.copy rfl (by rw [h]) else q ⟨i, h⟩,
      Walk.IsPath.nil, by simpa using hc, fun _ => Or.inl rfl, fun h => absurd rfl h, ?_, ?_, ?_,
      fun h => absurd rfl h⟩
    · intro i
      dsimp only
      split_ifs with h
      · simpa using hR.reverse
      · exact hqP _
    · intro i v hv
      dsimp only at hv
      split_ifs at hv with h
      · rw [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hv
        exact hRB v hv
      · exact hqB _ v hv
    · intro i j hij v hvi hvj
      refine ⟨?_, rfl⟩
      dsimp only at hvi hvj
      split_ifs at hvi hvj with h1 h2 h2
      · exact absurd (h1.trans h2.symm) hij
      · rw [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hvi
        exact hRS v hvi ⟨_, hvj⟩
      · rw [Walk.support_copy, Walk.support_reverse, List.mem_reverse] at hvj
        exact hRS v hvj ⟨_, hvi⟩
      · exact hqD _ _ (fun h => hij (congrArg Subtype.val h)) v hvi hvj
  have uniq : ∀ k, x ∈ (q k).support → k = m := by
    intro k hk
    by_contra hne
    exact hxc (hqD k m hne x hk hxm)
  have hm4 : m.1 ≠ i₄ := m.2
  have hTP : ((q m).takeUntil x hxm).IsPath := (hqP m).takeUntil hxm
  have hDP : ((q m).dropUntil x hxm).IsPath := (hqP m).dropUntil hxm
  have hTsub : ∀ v ∈ ((q m).takeUntil x hxm).support, v ∈ (q m).support :=
    fun v hv => (q m).support_takeUntil_subset_support hxm hv
  have hDsub : ∀ v ∈ ((q m).dropUntil x hxm).support, v ∈ (q m).support :=
    fun v hv => (q m).support_dropUntil_subset_support hxm hv
  have hTD : ∀ v ∈ ((q m).takeUntil x hxm).support, v ∈ ((q m).dropUntil x hxm).support →
      v = x := by
    intro v h1 h2
    have hPP : (((q m).takeUntil x hxm).append ((q m).dropUntil x hxm)).IsPath := by
      rw [Walk.take_spec]; exact hqP m
    exact append_path_meet _ _ hPP h1 h2
  generalize (q m).takeUntil x hxm = T at hTP hTsub hTD
  generalize (q m).dropUntil x hxm = D at hDP hDsub hTD
  have hcT : c ∈ T.support := T.start_mem_support
  obtain ⟨ctr, hctr⟩ : ∃ ctr : ι → V, ctr = fun i => if i = m.1 ∨ i = i₄ then x else c :=
    ⟨_, rfl⟩
  have hctr4 : ctr i₄ = x := by simp [hctr]
  have hctrm : ctr m.1 = x := by simp [hctr]
  have hctro : ∀ i, i ≠ i₄ → i ≠ m.1 → ctr i = c := by
    intro i h1 h2; simp [hctr, h1, h2]
  let p : ∀ i, G.Walk (ctr i) (a i) := fun i =>
    if h : i = i₄ then R.reverse.copy (by rw [h, hctr4]) (by rw [h])
    else if h' : i = m.1 then D.copy (by rw [h', hctrm]) (by rw [h'])
    else (q ⟨i, h⟩).copy (by rw [hctro i h h']) rfl
  have key : ∀ i, (p i).IsPath ∧ ((i = i₄ ∧ ∀ v, v ∈ (p i).support ↔ v ∈ R.support) ∨
      (i = m.1 ∧ ∀ v, v ∈ (p i).support ↔ v ∈ D.support) ∨
      (∃ h : i ≠ i₄, i ≠ m.1 ∧ ∀ v, v ∈ (p i).support ↔ v ∈ (q ⟨i, h⟩).support)) := by
    intro i
    simp only [p]
    split_ifs with h h'
    · exact ⟨by simpa using hR.reverse, Or.inl ⟨h, fun v => by simp⟩⟩
    · exact ⟨by simpa using hDP, Or.inr (Or.inl ⟨h', fun v => by simp⟩)⟩
    · exact ⟨by simpa using hqP _, Or.inr (Or.inr ⟨h, h', fun v => by simp⟩)⟩
  have hpB : ∀ i, ∀ v ∈ (p i).support, v ∈ B := by
    intro i v hv
    rcases (key i).2 with ⟨-, hs⟩ | ⟨-, hs⟩ | ⟨h, -, hs⟩ <;> rw [hs] at hv
    · exact hRB v hv
    · exact hqB m v (hDsub v hv)
    · exact hqB _ v hv
  refine ⟨c, hc, x, hRB x R.end_mem_support, T, ctr, p, hTP, fun v hv => hqB m v (hTsub v hv),
    ?_, ?_, fun i => (key i).1, hpB, ?_, ?_⟩
  · intro i
    rw [hctr]
    dsimp only
    split_ifs <;> simp
  · intro _
    have hf : (Finset.univ.filter fun i => ctr i = c) =
        Finset.univ.filter fun i => ¬(i = m.1 ∨ i = i₄) := by
      apply Finset.filter_congr
      intro i _
      rw [hctr]
      dsimp only
      split_ifs with h <;> simp [h, hxc]
    rw [hf]
    have h2 : (Finset.univ.filter fun i => i = m.1 ∨ i = i₄) = {m.1, i₄} := by
      ext; simp
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i => i = m.1 ∨ i = i₄)
    rw [h2, Finset.card_pair hm4, Finset.card_univ, hι] at this
    omega
  · intro i j hij v hvi hvj
    rcases (key i).2 with ⟨hi, hsi⟩ | ⟨hi, hsi⟩ | ⟨hi4, him, hsi⟩ <;> rw [hsi] at hvi
    · rcases (key j).2 with ⟨hj, hsj⟩ | ⟨hj, hsj⟩ | ⟨hj4, hjm, hsj⟩ <;> rw [hsj] at hvj
      · exact absurd (hi.trans hj.symm) hij
      · have := hRS v hvi ⟨m, hDsub v hvj⟩
        rw [hi, hctr4, hj, hctrm]
        exact ⟨this, rfl⟩
      · have := hRS v hvi ⟨_, hvj⟩
        rw [this] at hvj
        exact absurd (congrArg Subtype.val (uniq _ hvj)) hjm
    · rcases (key j).2 with ⟨hj, hsj⟩ | ⟨hj, hsj⟩ | ⟨hj4, hjm, hsj⟩ <;> rw [hsj] at hvj
      · have := hRS v hvj ⟨m, hDsub v hvi⟩
        rw [hi, hctrm, hj, hctr4]
        exact ⟨this, rfl⟩
      · exact absurd (hi.trans hj.symm) hij
      · have hvc := hqD m ⟨j, hj4⟩ (fun h => hjm (congrArg Subtype.val h).symm) v
          (hDsub v hvi) hvj
        rw [hvc] at hvi
        exact absurd (hTD c hcT hvi).symm hxc
    · rcases (key j).2 with ⟨hj, hsj⟩ | ⟨hj, hsj⟩ | ⟨hj4, hjm, hsj⟩ <;> rw [hsj] at hvj
      · have := hRS v hvj ⟨_, hvi⟩
        rw [this] at hvi
        exact absurd (congrArg Subtype.val (uniq _ hvi)) him
      · have hvc := hqD ⟨i, hi4⟩ m (fun h => him (congrArg Subtype.val h)) v hvi
          (hDsub v hvj)
        rw [hvc] at hvj
        exact absurd (hTD c hcT hvj).symm hxc
      · have hvc := hqD ⟨i, hi4⟩ ⟨j, hj4⟩ (fun h => hij (congrArg Subtype.val h)) v hvi hvj
        rw [hctro i hi4 him, hctro j hj4 hjm]
        exact ⟨hvc, rfl⟩
  · intro _ i v hvi hvr
    rcases (key i).2 with ⟨hi, hsi⟩ | ⟨hi, hsi⟩ | ⟨hi4, him, hsi⟩ <;> rw [hsi] at hvi
    · rw [hi, hctr4]
      exact hRS v hvi ⟨m, hTsub v hvr⟩
    · rw [hi, hctrm]
      exact hTD v hvr hvi
    · rw [hctro i hi4 him]
      exact hqD ⟨i, hi4⟩ m (fun h => him (congrArg Subtype.val h)) v hvi (hTsub v hvr)

end Kuratowski
