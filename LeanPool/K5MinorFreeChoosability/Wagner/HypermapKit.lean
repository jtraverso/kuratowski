/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Embedding

/-!
# A toolkit of exact hypermap surgery

This file provides the elementary operations on hypermaps `(σ, α)` used to build rotation
systems in the proof of Wagner's planarity criterion, together with their exact effect on the
Euler defect.

* `eulerDefect_mulSwap_left_eq`, `eulerDefect_mulSwap_right_eq`: master formulas for the
  change of the defect under `σ ↦ σ * swap p q` and `α ↦ α * swap c d`.
* `eulerDefect_mulSwap_merge_of_not_rel`: merging two darts of different components does not
  change the defect.
* `eulerDefect_mulSwap_le_of_face`: splitting or merging `σ`-cycles at two corners of the same
  face never increases the defect.
* `eulerDefect_mulSwap_right_le`: joining two free darts lying in the same face by an edge never
  increases the defect.
* `eulerDefect_uncontract_le`: splitting a vertex by a new edge never increases the defect.
* `insertBefore`: inserting a free dart into a rotation, with its exact effect.
* `isPlanar_of_hypermap`: a hypermap of defect `≤ 0` labelled bijectively by the darts of `G`,
  compatibly with tails and reversal and with at most one rotation cycle per non-isolated vertex,
  yields a plane map of `G`.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {D : Type*}

theorem compSetoid_comm {σ α : Perm D} {a b : D} :
    compSetoid σ α a b ↔ compSetoid α σ a b := by
  constructor
  · intro h
    exact compSetoid_le (compSetoid α σ) (compSetoid_right α σ) (compSetoid_left α σ) h
  · intro h
    exact compSetoid_le (compSetoid σ α) (compSetoid_right σ α) (compSetoid_left σ α) h

theorem numComponents_comm (σ α : Perm D) : numComponents σ α = numComponents α σ :=
  numClasses_congr fun _ _ => compSetoid_comm

/-- Elements of a fixed point's component are equal to it. -/
theorem eq_of_compSetoid_fixed {σ α : Perm D} {n u : D} (hσ : σ n = n) (hα : α n = n)
    (h : compSetoid σ α n u) : u = n := by
  have key := compSetoid_le (Setoid.ker fun w => (w = n : Prop))
    (fun z => by
      rw [Setoid.ker_def]
      exact propext ⟨fun hz => by rw [hz, hσ], fun hz => σ.injective (hz.trans hσ.symm)⟩)
    (fun z => by
      rw [Setoid.ker_def]
      exact propext ⟨fun hz => by rw [hz, hα], fun hz => α.injective (hz.trans hα.symm)⟩) h
  rw [Setoid.ker_def] at key
  exact key ▸ rfl

section Kit

variable [DecidableEq D]

theorem mulSwap_mul_eq (σ α : Perm D) (p q : D) :
    σ * swap p q * α = σ * α * swap (α⁻¹ p) (α⁻¹ q) := by
  have h := swap_apply_apply α (α⁻¹ p) (α⁻¹ q)
  rw [show α (α⁻¹ p) = p by simp, show α (α⁻¹ q) = q by simp] at h
  rw [h]
  simp [mul_assoc]

theorem eulerDefect_mulSwap_left_eq (σ α : Perm D) (p q : D) :
    eulerDefect (σ * swap p q) α = eulerDefect σ α +
      2 * ((numComponents (σ * swap p q) α : ℤ) - numComponents σ α) -
      ((cycleCount (σ * swap p q) : ℤ) - cycleCount σ) -
      ((cycleCount (σ * α * swap (α⁻¹ p) (α⁻¹ q)) : ℤ) - cycleCount (σ * α)) := by
  unfold eulerDefect
  rw [mulSwap_mul_eq]
  ring

theorem eulerDefect_mulSwap_right_eq (σ α : Perm D) (c d : D) :
    eulerDefect σ (α * swap c d) = eulerDefect σ α +
      2 * ((numComponents σ (α * swap c d) : ℤ) - numComponents σ α) -
      ((cycleCount (α * swap c d) : ℤ) - cycleCount α) -
      ((cycleCount (σ * α * swap c d) : ℤ) - cycleCount (σ * α)) := by
  unfold eulerDefect
  rw [← mul_assoc]
  ring

theorem compSetoid_mulSwap_left_le_addPair (σ α : Perm D) (p q : D) {u v : D}
    (h : compSetoid σ α u v) : addPairSetoid (compSetoid (σ * swap p q) α) p q u v :=
  compSetoid_le _ (addPair_apply_of_mulSwap _ σ p q (compSetoid_left _ _))
    (fun z => Or.inl (compSetoid_right _ _ z)) h

variable [Finite D]

theorem numComponents_mulSwap_left_le_succ (σ α : Perm D) (p q : D) :
    numComponents (σ * swap p q) α ≤ numComponents σ α + 1 := by
  have h1 := numClasses_le_addPair_succ (compSetoid (σ * swap p q) α) p q
  have h2 := numClasses_le_of_le (fun u v h => compSetoid_mulSwap_left_le_addPair σ α p q h)
  unfold numComponents
  omega

theorem numComponents_mulSwap_left_le_of_rel {σ α : Perm D} {p q : D}
    (h : compSetoid (σ * swap p q) α p q) :
    numComponents (σ * swap p q) α ≤ numComponents σ α :=
  numClasses_le_of_le fun _ _ huv =>
    compSetoid_le _ (rel_apply_of_mulSwap _ σ p q (compSetoid_left _ _) h)
      (compSetoid_right _ _) huv

theorem numComponents_mulSwap_left_of_not {σ α : Perm D} {p q : D}
    (h : ¬ compSetoid σ α p q) :
    numComponents σ α = numComponents (σ * swap p q) α + 1 := by
  have hs : ¬ SameCycle σ p q := fun hs => h (compSetoid_of_sameCycle_left hs)
  have hpq : compSetoid (σ * swap p q) α p q :=
    compSetoid_of_sameCycle_left (sameCycle_mulSwap_of_not hs)
  have hold : ∀ u v, compSetoid σ α u v → compSetoid (σ * swap p q) α u v := fun u v huv =>
    compSetoid_le _ (rel_apply_of_mulSwap _ σ p q (compSetoid_left _ _) hpq)
      (compSetoid_right _ _) huv
  have hiff : ∀ u v, compSetoid (σ * swap p q) α u v ↔ addPairSetoid (compSetoid σ α) p q u v := by
    intro u v
    constructor
    · intro huv
      refine compSetoid_le _ (addPair_apply_of_mulSwap _ (σ * swap p q) p q ?_)
        (fun z => Or.inl (compSetoid_right _ _ z)) huv
      intro z
      rw [mulSwap_mulSwap]
      exact compSetoid_left _ _ z
    · rintro (k | ⟨k1, k2⟩ | ⟨k1, k2⟩)
      · exact hold _ _ k
      · exact (compSetoid _ _).trans (hold _ _ k1) ((compSetoid _ _).trans hpq (hold _ _ k2))
      · exact (compSetoid _ _).trans (hold _ _ k1)
          ((compSetoid _ _).trans ((compSetoid _ _).symm hpq) (hold _ _ k2))
  have h1 := numClasses_addPair_of_not (s := compSetoid σ α) h
  have h2 : numComponents (σ * swap p q) α = numClasses (addPairSetoid (compSetoid σ α) p q) :=
    numClasses_congr hiff
  unfold numComponents at h2 ⊢
  omega

/-- Merging two darts of different components does not change the defect. -/
theorem eulerDefect_mulSwap_merge_of_not_rel {σ α : Perm D} {p q : D}
    (h : ¬ compSetoid σ α p q) : eulerDefect (σ * swap p q) α = eulerDefect σ α := by
  have hs : ¬ SameCycle σ p q := fun hs => h (compSetoid_of_sameCycle_left hs)
  have hf : ¬ SameCycle (σ * α) (α⁻¹ p) (α⁻¹ q) := by
    intro hf
    have h1 := compSetoid_of_sameCycle_mul hf
    have hp : compSetoid σ α (α⁻¹ p) p := by
      have := compSetoid_right σ α (α⁻¹ p); simpa using this
    have hq : compSetoid σ α (α⁻¹ q) q := by
      have := compSetoid_right σ α (α⁻¹ q); simpa using this
    exact h ((compSetoid _ _).trans ((compSetoid _ _).symm hp) ((compSetoid _ _).trans h1 hq))
  have e1 := cycleCount_mul_swap_of_not_sameCycle hs
  have e2 := cycleCount_mul_swap_of_not_sameCycle hf
  have e3 := numComponents_mulSwap_left_of_not h
  rw [eulerDefect_mulSwap_left_eq]
  push_cast [← e1, ← e2, e3]
  ring

/-- Splitting or merging `σ`-cycles at two corners of the same face never increases the
defect. -/
theorem eulerDefect_mulSwap_le_of_face {σ α : Perm D} {p q : D} (hpq : p ≠ q)
    (hf : SameCycle (σ * α) (α⁻¹ p) (α⁻¹ q)) :
    eulerDefect (σ * swap p q) α ≤ eulerDefect σ α := by
  have hpq' : α⁻¹ p ≠ α⁻¹ q := fun e => hpq (by simpa using congrArg α e)
  have e2 := cycleCount_mul_swap_of_sameCycle hpq' hf
  rw [eulerDefect_mulSwap_left_eq, e2]
  by_cases hs : SameCycle σ p q
  · have e1 := cycleCount_mul_swap_of_sameCycle hpq hs
    have hK := numComponents_mulSwap_left_le_succ σ α p q
    rw [e1]
    push_cast
    omega
  · have e1 := cycleCount_mul_swap_of_not_sameCycle hs
    have hK := numComponents_mulSwap_left_le_of_rel
      (compSetoid_of_sameCycle_left (α := α) (sameCycle_mulSwap_of_not hs))
    rw [← e1]
    push_cast
    omega

/-- Exact defect change when splitting a `σ`-cycle at two corners of the same face. -/
theorem eulerDefect_mulSwap_split_face_eq {σ α : Perm D} {p q : D} (hpq : p ≠ q)
    (hs : SameCycle σ p q) (hf : SameCycle (σ * α) (α⁻¹ p) (α⁻¹ q)) :
    eulerDefect (σ * swap p q) α = eulerDefect σ α +
      2 * ((numComponents (σ * swap p q) α : ℤ) - numComponents σ α) - 2 := by
  have hpq' : α⁻¹ p ≠ α⁻¹ q := fun e => hpq (by simpa using congrArg α e)
  have e2 := cycleCount_mul_swap_of_sameCycle hpq' hf
  have e1 := cycleCount_mul_swap_of_sameCycle hpq hs
  rw [eulerDefect_mulSwap_left_eq, e2, e1]
  push_cast
  ring

/-- Exact defect change when splitting a `σ`-cycle at two corners of different faces. -/
theorem eulerDefect_mulSwap_split_noface_eq {σ α : Perm D} {p q : D} (hpq : p ≠ q)
    (hs : SameCycle σ p q) (hf : ¬ SameCycle (σ * α) (α⁻¹ p) (α⁻¹ q)) :
    eulerDefect (σ * swap p q) α = eulerDefect σ α +
      2 * ((numComponents (σ * swap p q) α : ℤ) - numComponents σ α) := by
  have e2 := cycleCount_mul_swap_of_not_sameCycle hf
  have e1 := cycleCount_mul_swap_of_sameCycle hpq hs
  rw [eulerDefect_mulSwap_left_eq, e1, ← e2]
  push_cast
  ring

/-- Joining two free darts of the same face by an edge never increases the defect. -/
theorem eulerDefect_mulSwap_right_le {σ α : Perm D} {c d : D} (hcd : c ≠ d) (hc : α c = c)
    (hd : α d = d) (hf : SameCycle (σ * α) c d) :
    eulerDefect σ (α * swap c d) ≤ eulerDefect σ α := by
  have hα : ¬ SameCycle α c d := fun h => hcd (h.eq_of_left hc)
  have e1 := cycleCount_mul_swap_of_not_sameCycle hα
  have e2 := cycleCount_mul_swap_of_sameCycle hcd hf
  have hrel : compSetoid (α * swap c d) σ c d := by
    have := compSetoid_left (α * swap c d) σ c
    simpa [hd] using this
  have hK' := numComponents_mulSwap_left_le_of_rel hrel
  have hK : numComponents σ (α * swap c d) ≤ numComponents σ α := by
    rw [numComponents_comm σ, numComponents_comm σ]; exact hK'
  rw [eulerDefect_mulSwap_right_eq, e2, ← e1]
  push_cast
  omega

/-- Splitting a vertex by a new edge `{a, b}` (two free darts of the same rotation cycle) never
increases the defect. -/
theorem eulerDefect_uncontract_le {σ α : Perm D} {a b : D} (hab : a ≠ b) (ha : α a = a)
    (hb : α b = b) (hs : SameCycle σ a b) :
    eulerDefect (σ * swap a b) (α * swap a b) ≤ eulerDefect σ α := by
  have hcomm : α * swap a b = swap a b * α := by
    ext z
    simp only [Perm.mul_apply]
    by_cases hza : z = a
    · subst hza; simp [ha, hb]
    by_cases hzb : z = b
    · subst hzb; simp [ha, hb]
    have h1 : α z ≠ a := fun e => hza (α.injective (e.trans ha.symm))
    have h2 : α z ≠ b := fun e => hzb (α.injective (e.trans hb.symm))
    rw [swap_apply_of_ne_of_ne hza hzb, swap_apply_of_ne_of_ne h1 h2]
  have hφ : σ * swap a b * (α * swap a b) = σ * α := by
    rw [hcomm, ← mul_assoc, mul_assoc σ, swap_mul_self, mul_one]
  have hα : ¬ SameCycle α a b := fun h => hab (h.eq_of_left ha)
  have e1 := cycleCount_mul_swap_of_sameCycle hab hs
  have e2 := cycleCount_mul_swap_of_not_sameCycle hα
  have hab' : compSetoid (σ * swap a b) (α * swap a b) a b := by
    have := compSetoid_right (σ * swap a b) (α * swap a b) a
    simpa [hb] using this
  have hK : numComponents (σ * swap a b) (α * swap a b) ≤ numComponents σ α :=
    numClasses_le_of_le fun _ _ huv =>
      compSetoid_le _ (rel_apply_of_mulSwap _ σ a b (compSetoid_left _ _) hab')
        (rel_apply_of_mulSwap _ α a b (compSetoid_right _ _) hab') huv
  unfold eulerDefect
  rw [hφ, e1, ← e2]
  push_cast
  omega

end Kit

/-! ### Inserting a free dart into a rotation -/

section Insert

variable [DecidableEq D]

/-- Insert the dart `n` into the cycle of `σ` immediately before `h`. -/
def insertBefore (σ : Perm D) (h n : D) : Perm D := σ * swap (σ⁻¹ h) n

variable {σ : Perm D} {h n : D}

theorem insertBefore_apply_pred (hσn : σ n = n) (hhn : h ≠ n) :
    insertBefore σ h n (σ⁻¹ h) = n := by
  have : σ⁻¹ h ≠ n := fun e => hhn (by rw [← hσn, ← e]; simp)
  simp [insertBefore, hσn]

theorem insertBefore_apply_new : insertBefore σ h n n = h := by
  simp [insertBefore]

theorem insertBefore_apply_of_ne {u : D} (h1 : u ≠ σ⁻¹ h) (h2 : u ≠ n) :
    insertBefore σ h n u = σ u := by
  change σ (swap (σ⁻¹ h) n u) = σ u
  rw [swap_apply_of_ne_of_ne h1 h2]

theorem insertBefore_inv_apply_new : (insertBefore σ h n)⁻¹ h = n := by
  rw [Perm.inv_eq_iff_eq, insertBefore_apply_new]

theorem sameCycle_insertBefore (hσn : σ n = n) {u v : D} (huv : SameCycle σ u v) :
    SameCycle (insertBefore σ h n) u v := by
  refine sameCycle_of_step (SameCycle.setoid (insertBefore σ h n)) (fun z => ?_) huv
  change SameCycle _ z (σ z)
  by_cases hz1 : z = σ⁻¹ h
  · by_cases hhn : h = n
    · subst hhn
      have : z = h := by rw [hz1]; exact (Perm.inv_eq_iff_eq).2 hσn.symm
      subst this
      rw [hσn]
    · have e1 : insertBefore σ h n z = n := by rw [hz1]; exact insertBefore_apply_pred hσn hhn
      have e2 : insertBefore σ h n n = h := insertBefore_apply_new
      have : σ z = h := by rw [hz1]; simp
      rw [this]
      exact ⟨2, by rw [zpow_two, Perm.mul_apply, e1, e2]⟩
  by_cases hz2 : z = n
  · subst hz2; rw [hσn]
  · rw [← insertBefore_apply_of_ne hz1 hz2]
    exact ⟨1, by simp⟩

theorem sameCycle_insertBefore_new : SameCycle (insertBefore σ h n) n h :=
  ⟨1, by simp [insertBefore_apply_new]⟩

variable [Finite D]

theorem cycleCount_insertBefore (hσn : σ n = n) (hhn : h ≠ n) :
    cycleCount (insertBefore σ h n) + 1 = cycleCount σ := by
  have hne : σ⁻¹ h ≠ n := fun e => hhn (by rw [← hσn, ← e]; simp)
  refine cycleCount_mul_swap_of_not_sameCycle fun hs => hne ?_
  exact (hs.symm.eq_of_left hσn).symm

theorem eulerDefect_insertBefore {α : Perm D} (hσn : σ n = n) (hαn : α n = n) (hhn : h ≠ n) :
    eulerDefect (insertBefore σ h n) α = eulerDefect σ α := by
  have hne : σ⁻¹ h ≠ n := fun e => hhn (by rw [← hσn, ← e]; simp)
  refine eulerDefect_mulSwap_merge_of_not_rel fun hr => hne ?_
  exact eq_of_compSetoid_fixed hσn hαn ((compSetoid _ _).symm hr)

end Insert

/-! ### Cycles after merging -/

theorem sameCycle_mulSwap_of_not_left [DecidableEq D] [Finite D] {π : Perm D} {x y u : D}
    (h : ¬ SameCycle π x y) (hu : SameCycle π x u) : SameCycle (π * swap x y) x u := by
  have hxy := sameCycle_mulSwap_of_not h
  rcases sameCycle_le_addPair_mulSwap π x y hu with k | ⟨_, k2⟩ | ⟨_, k2⟩
  · exact k
  · exact hxy.trans k2
  · exact k2

theorem sameCycle_mulSwap_of_not_right [DecidableEq D] [Finite D] {π : Perm D} {x y u : D}
    (h : ¬ SameCycle π x y) (hu : SameCycle π y u) : SameCycle (π * swap x y) x u := by
  have hxy := sameCycle_mulSwap_of_not h
  have h' : ¬ SameCycle π y x := fun e => h e.symm
  have := sameCycle_mulSwap_of_not_left h' hu
  rw [swap_comm] at this
  exact hxy.trans this

/-! ### Realising a hypermap as a plane map -/

/-- A permutation preserving a labelling, with at most as many cycles as labels, has exactly
one cycle per label. -/
theorem sameCycle_of_cycleCount_le [Finite D] {β : Type*} (π : Perm D) (f : D → β)
    (hf : ∀ d, f (π d) = f d) (hc : cycleCount π ≤ Nat.card (Set.range f)) {d e : D}
    (hde : f d = f e) : SameCycle π d e := by
  let g : Quotient (SameCycle.setoid π) → Set.range f :=
    Quotient.lift (fun d => ⟨f d, d, rfl⟩) (fun a b (hab : SameCycle π a b) =>
      Subtype.ext (by
        change f a = f b
        exact sameCycle_of_step (Setoid.ker f) (fun z => by
          rw [Setoid.ker_def]; exact (hf z).symm) hab))
  have hsurj : Function.Surjective g := by
    rintro ⟨_, d, rfl⟩
    exact ⟨Quotient.mk _ d, rfl⟩
  have hbij := hsurj.bijective_of_nat_card_le hc
  have := hbij.1 (a₁ := Quotient.mk _ d) (a₂ := Quotient.mk _ e) (Subtype.ext hde)
  exact Quotient.exact this

theorem natCard_range_fst (G : SimpleGraph V) :
    Nat.card (Set.range fun d : G.Dart => d.fst) = Nat.card {v // ∃ u, G.Adj v u} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  constructor
  · rintro ⟨d, rfl⟩; exact ⟨d.snd, d.adj⟩
  · rintro ⟨u, h⟩; exact ⟨⟨(v, u), h⟩, rfl⟩

/-- **Realisation**: a hypermap of defect at most zero whose darts are labelled bijectively by
the darts of `G`, compatibly with reversal and tails, and with at most one rotation cycle per
non-isolated vertex, gives a plane map of `G`. -/
theorem isPlanar_of_hypermap [Finite D] {V : Type*} [Finite V] {G : SimpleGraph V}
    (σ α : Perm D) (hdef : eulerDefect σ α ≤ 0) (τ : D → G.Dart) (hτ : Function.Bijective τ)
    (hα : ∀ d, τ (α d) = (τ d).symm) (hσ : ∀ d, (τ (σ d)).fst = (τ d).fst)
    (hc : cycleCount σ ≤ Nat.card {v // ∃ u, G.Adj v u}) : IsPlanar G := by
  classical
  let e := Equiv.ofBijective τ hτ
  have he : ∀ d, e d = τ d := fun _ => rfl
  have : Finite G.Dart := Finite.of_equiv D e
  have hpc : ∀ (π : Perm D) d, (e.permCongr π) d = τ (π (e.symm d)) := fun π d => by
    simp [Equiv.permCongr_apply, he]
  have hrot : ∀ d, (e.permCongr σ) d = τ (σ (e.symm d)) := hpc σ
  have hsymm : e.permCongr α = dartSymm G := by
    refine Equiv.ext fun d => ?_
    rw [hpc, hα, ← he, Equiv.apply_symm_apply]
    rfl
  have hfst : ∀ d, ((e.permCongr σ) d).fst = d.fst := fun d => by
    rw [hrot, hσ, ← he, Equiv.apply_symm_apply]
  have hcc : cycleCount (e.permCongr σ) ≤ Nat.card (Set.range fun d : G.Dart => d.fst) := by
    rw [cycleCount_permCongr, natCard_range_fst]
    exact hc
  refine ⟨⟨e.permCongr σ, ⟨hfst, fun d d' hdd => ?_⟩, ?_⟩⟩
  · exact sameCycle_of_cycleCount_le _ (fun d : G.Dart => d.fst) hfst hcc hdd
  · rw [← hsymm, eulerDefect_permCongr]
    exact le_antisymm hdef (eulerDefect_nonneg σ α)

end LeanPool.K5MinorFreeChoosability
