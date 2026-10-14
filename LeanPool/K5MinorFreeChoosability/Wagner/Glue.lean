/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.GlueKit

/-!
# Gluing plane maps along at most two vertices

`isPlanar_sup_of_sep`: if `GA` has its edges in `A`, `GB` has its edges in `B`,
`|A ∩ B| ≤ 2`, and `A ∩ B` is a clique in both graphs, then planarity of `GA` and `GB` implies
planarity of `GA ⊔ GB`.  The rotation systems are combined on the disjoint union of the dart
sets: for a common vertex `u` the two rotations at `u` are merged (different components, so
the Euler defect is unchanged); for a second common vertex `v` the rotations at `v` are merged
at two corners of one face, and the duplicated copy of the edge `uv` is removed.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

/-- Realisation on a subset of darts: darts outside `P` must be fixed by both permutations. -/
theorem isPlanar_of_hypermap_sub {D : Type*} [Finite D] {V : Type*} [Finite V]
    {G : SimpleGraph V} (P : D → Prop) (σ α : Perm D)
    (hfix : ∀ x, ¬ P x → σ x = x ∧ α x = x) (hdef : eulerDefect σ α ≤ 0) (τ : D → G.Dart)
    (hα : ∀ x, P x → τ (α x) = (τ x).symm) (hσ : ∀ x, P x → (τ (σ x)).fst = (τ x).fst)
    (hinj : ∀ x y, P x → P y → τ x = τ y → x = y) (hsurj : ∀ e, ∃ x, P x ∧ τ x = e)
    (hc : cycleCount σ ≤ Nat.card {v // ∃ u, G.Adj v u} + Nat.card {x // ¬ P x}) :
    IsPlanar G := by
  classical
  have hP : ∀ (π : Perm D), (∀ x, ¬ P x → π x = x) → ∀ x, P (π x) ↔ P x := by
    intro π hπ x
    constructor
    · intro h
      by_contra hx
      rw [hπ x hx] at h
      exact hx h
    · intro h
      by_contra hx
      have : π (π x) = π x := hπ _ hx
      exact hx (by rw [π.injective this]; exact h)
  have hσP := hP σ (fun x hx => (hfix x hx).1)
  have hαP := hP α (fun x hx => (hfix x hx).2)
  have hσ' : ofSubtype (σ.subtypePerm hσP) = σ :=
    ofSubtype_subtypePerm _ (fun x hx => by_contra fun h => hx (hfix x h).1)
  have hα' : ofSubtype (α.subtypePerm hαP) = α :=
    ofSubtype_subtypePerm _ (fun x hx => by_contra fun h => hx (hfix x h).2)
  refine isPlanar_of_hypermap (σ.subtypePerm hσP) (α.subtypePerm hαP) ?_
    (fun x => τ x.1) ⟨fun x y h => Subtype.ext (hinj _ _ x.2 y.2 h), fun e => ?_⟩
    (fun x => hα x.1 x.2) (fun x => hσ x.1 x.2) ?_
  · rw [← eulerDefect_ofSubtype, hσ', hα']
    exact hdef
  · obtain ⟨x, hx, rfl⟩ := hsurj e
    exact ⟨⟨x, hx⟩, rfl⟩
  · have := cycleCount_ofSubtype P (σ.subtypePerm hσP)
    rw [hσ'] at this
    omega

variable {V : Type*} [Finite V] [DecidableEq V]

section Glue

variable {GA GB : SimpleGraph V}

/-- The darts of `GA ⊔ GB` coming from the darts of `GA` and of `GB`. -/
def sumDart : GA.Dart ⊕ GB.Dart → (GA ⊔ GB).Dart :=
  Sum.elim (fun d => ⟨d.toProd, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl d.adj)⟩)
    (fun d => ⟨d.toProd, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr d.adj)⟩)

omit [Finite V] [DecidableEq V] in
theorem sumDart_toProd (x : GA.Dart ⊕ GB.Dart) :
    (sumDart x).toProd =
      Sum.elim (fun d : GA.Dart => d.toProd) (fun d : GB.Dart => d.toProd) x := by
  rcases x with d | d <;> rfl

omit [Finite V] [DecidableEq V] in
theorem sumDart_symm (x : GA.Dart ⊕ GB.Dart) :
    sumDart (Perm.sumCongr (dartSymm GA) (dartSymm GB) x) = (sumDart x).symm := by
  rcases x with d | d <;> rfl

omit [Finite V] [DecidableEq V] in
theorem sumDart_surj (e : (GA ⊔ GB).Dart) : ∃ x, sumDart x = e := by
  rcases (SimpleGraph.sup_adj _ _ _ _).1 e.adj with h | h
  · exact ⟨Sum.inl ⟨e.toProd, h⟩, rfl⟩
  · exact ⟨Sum.inr ⟨e.toProd, h⟩, rfl⟩

omit [DecidableEq V] in
theorem natCard_nonisolated_sup :
    Nat.card {v // ∃ u, GA.Adj v u} + Nat.card {v // ∃ u, GB.Adj v u} =
      Nat.card {v // ∃ u, (GA ⊔ GB).Adj v u} +
        Nat.card {v // (∃ u, GA.Adj v u) ∧ (∃ u, GB.Adj v u)} := by
  rw [← natCard_or_add_and]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
    simp only [SimpleGraph.sup_adj]
    exact ⟨fun h => h.elim (fun ⟨u, hu⟩ => ⟨u, Or.inl hu⟩) (fun ⟨u, hu⟩ => ⟨u, Or.inr hu⟩),
      fun ⟨u, hu⟩ => hu.elim (fun h => Or.inl ⟨u, h⟩) (fun h => Or.inr ⟨u, h⟩)⟩)

end Glue

section Glue2

variable {GA GB : SimpleGraph V} {A B : Finset V} (hA : ∀ u v, GA.Adj u v → u ∈ A)
  (hB : ∀ u v, GB.Adj u v → u ∈ B)
include hA hB

omit [Finite V] in
theorem mem_inter_of_toProd_eq {a : GA.Dart} {b : GB.Dart} (h : a.toProd = b.toProd) :
    a.fst ∈ A ∩ B ∧ a.snd ∈ A ∩ B := by
  have h1 : a.fst = b.fst := congrArg Prod.fst h
  have h2 : a.snd = b.snd := congrArg Prod.snd h
  refine ⟨Finset.mem_inter.2 ⟨hA _ _ a.adj, h1 ▸ hB _ _ b.adj⟩,
    Finset.mem_inter.2 ⟨hA _ _ a.adj.symm, h2 ▸ hB _ _ b.adj.symm⟩⟩

/-- Gluing along at most one vertex. -/
theorem isPlanar_sup_of_le_one (MA : PlaneMap GA) (MB : PlaneMap GB)
    (h1 : ∀ p ∈ A ∩ B, ∀ q ∈ A ∩ B, p = q) : IsPlanar (GA ⊔ GB) := by
  classical
  have := Fintype.ofFinite V
  set σ0 := Perm.sumCongr MA.rot MB.rot with hσ0
  set α0 := Perm.sumCongr (dartSymm GA) (dartSymm GB) with hα0
  have hdef0 : eulerDefect σ0 α0 = 0 := by
    rw [hσ0, hα0, eulerDefect_sumCongr, MA.eulerDefect_eq_zero, MB.eulerDefect_eq_zero,
      add_zero]
  have hF0 : ∀ x, (sumDart (σ0 x)).fst = (sumDart x).fst := by
    rintro (d | d)
    · exact MA.isRotationSystem.fst_apply d
    · exact MB.isRotationSystem.fst_apply d
  have hc0 : cycleCount σ0 = Nat.card {v // ∃ u, GA.Adj v u} + Nat.card {v // ∃ u, GB.Adj v u} := by
    rw [hσ0, cycleCount_sumCongr, cycleCount_eq_card_nonisolated MA.isRotationSystem,
      cycleCount_eq_card_nonisolated MB.isRotationSystem]
  have hnon := natCard_nonisolated_sup (GA := GA) (GB := GB)
  have hcommon : ∀ v, (∃ u, GA.Adj v u) → (∃ u, GB.Adj v u) → v ∈ A ∩ B :=
    fun v ⟨u, hu⟩ ⟨u', hu'⟩ => Finset.mem_inter.2 ⟨hA v u hu, hB v u' hu'⟩
  have hinj : ∀ x y : GA.Dart ⊕ GB.Dart, sumDart x = sumDart y → x = y := by
    rintro (a | b) (a' | b') h <;> have h' := congrArg SimpleGraph.Dart.toProd h
    · exact congrArg Sum.inl ((SimpleGraph.Dart.ext_iff _ _).2 h')
    · exfalso
      obtain ⟨k1, k2⟩ := mem_inter_of_toProd_eq hA hB (a := a) (b := b') h'
      exact a.adj.ne (h1 _ k1 _ k2)
    · exfalso
      obtain ⟨k1, k2⟩ := mem_inter_of_toProd_eq hA hB (a := a') (b := b) h'.symm
      exact a'.adj.ne (h1 _ k1 _ k2)
    · exact congrArg Sum.inr ((SimpleGraph.Dart.ext_iff _ _).2 h')
  have hsurj : ∀ e : (GA ⊔ GB).Dart, ∃ x, True ∧ sumDart x = e := fun e => by
    obtain ⟨x, hx⟩ := sumDart_surj e
    exact ⟨x, trivial, hx⟩
  by_cases hu : ∃ (dA : GA.Dart) (dB : GB.Dart), dA.fst = dB.fst
  · obtain ⟨dA, dB, hfst⟩ := hu
    refine isPlanar_of_hypermap_sub (fun _ => True) (σ0 * swap (Sum.inl dA) (Sum.inr dB)) α0
      (fun x hx => absurd trivial hx) ?_ sumDart (fun x _ => sumDart_symm x)
      (fun x _ => mulSwap_preserves (fun x => (sumDart x).fst) hF0
        (a := Sum.inl dA) (b := Sum.inr dB) hfst x)
      (fun x y _ _ h => hinj x y h) hsurj ?_
    · rw [eulerDefect_mulSwap_merge_of_not_rel (not_compSetoid_sumCongr dA dB), hdef0]
    · have hc := cycleCount_mul_swap_of_not_sameCycle (π := σ0) (not_sameCycle_sumCongr dA dB)
      have hcom : Nat.card {v // (∃ u, GA.Adj v u) ∧ (∃ u, GB.Adj v u)} ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext
          (h1 _ (hcommon _ a.2.1 a.2.2) _ (hcommon _ b.2.1 b.2.2))⟩
      omega
  · push Not at hu
    refine isPlanar_of_hypermap_sub (fun _ => True) σ0 α0 (fun x hx => absurd trivial hx)
      hdef0.le sumDart (fun x _ => sumDart_symm x) (fun x _ => hF0 x)
      (fun x y _ _ h => hinj x y h) hsurj ?_
    have : IsEmpty {v // (∃ u, GA.Adj v u) ∧ (∃ u, GB.Adj v u)} :=
      ⟨fun ⟨v, ⟨u, h⟩, ⟨u', h'⟩⟩ => hu ⟨(v, u), h⟩ ⟨(v, u'), h'⟩ rfl⟩
    have hcom : Nat.card {v // (∃ u, GA.Adj v u) ∧ (∃ u, GB.Adj v u)} = 0 := Nat.card_of_isEmpty
    omega

/-- Gluing along an edge `uv` present in both graphs (a 2-sum keeping the edge). -/
theorem isPlanar_sup_of_two (MA : PlaneMap GA) (MB : PlaneMap GB) {u v : V} (huv : u ≠ v)
    (hK : A ∩ B = {u, v}) (hAuv : GA.Adj u v) (hBuv : GB.Adj u v) : IsPlanar (GA ⊔ GB) := by
  classical
  have := Fintype.ofFinite V
  set σ0 := Perm.sumCongr MA.rot MB.rot with hσ0
  set α0 := Perm.sumCongr (dartSymm GA) (dartSymm GB) with hα0
  have hdef0 : eulerDefect σ0 α0 = 0 := by
    rw [hσ0, hα0, eulerDefect_sumCongr, MA.eulerDefect_eq_zero, MB.eulerDefect_eq_zero,
      add_zero]
  let F : GA.Dart ⊕ GB.Dart → V := fun x => (sumDart x).fst
  have hF0 : ∀ x, F (σ0 x) = F x := by
    rintro (d | d)
    · exact MA.isRotationSystem.fst_apply d
    · exact MB.isRotationSystem.fst_apply d
  have hc0 : cycleCount σ0 = Nat.card {v // ∃ u, GA.Adj v u} + Nat.card {v // ∃ u, GB.Adj v u} := by
    rw [hσ0, cycleCount_sumCongr, cycleCount_eq_card_nonisolated MA.isRotationSystem,
      cycleCount_eq_card_nonisolated MB.isRotationSystem]
  have hnon := natCard_nonisolated_sup (GA := GA) (GB := GB)
  have hcommon : ∀ v, (∃ u, GA.Adj v u) → (∃ u, GB.Adj v u) → v ∈ A ∩ B :=
    fun v ⟨u, hu⟩ ⟨u', hu'⟩ => Finset.mem_inter.2 ⟨hA v u hu, hB v u' hu'⟩
  let pA : GA.Dart := ⟨(u, v), hAuv⟩
  let pB : GB.Dart := ⟨(u, v), hBuv⟩
  have hσ0l : ∀ d, σ0 (Sum.inl d) = Sum.inl (MA.rot d) := fun d => rfl
  have hσ0r : ∀ d, σ0 (Sum.inr d) = Sum.inr (MB.rot d) := fun d => rfl
  have hα0l : ∀ d, α0 (Sum.inl d) = Sum.inl d.symm := fun d => rfl
  have hα0r : ∀ d, α0 (Sum.inr d) = Sum.inr d.symm := fun d => rfl
  have hne_of_F : ∀ x y, F x ≠ F y → x ≠ y := fun x y h e => h (e ▸ rfl)
  set p : GA.Dart ⊕ GB.Dart := Sum.inl (MA.rot⁻¹ pA.symm) with hp
  set q : GA.Dart ⊕ GB.Dart := Sum.inr (MB.rot⁻¹ pB.symm) with hq
  have hFp : F p = v := by
    change (MA.rot⁻¹ pA.symm).fst = v
    rw [MA.fst_rot_inv]
    rfl
  have hFq : F q = v := by
    change (MB.rot⁻¹ pB.symm).fst = v
    rw [MB.fst_rot_inv]
    rfl
  have hFpA : F (Sum.inl pA) = u := rfl
  have hFpB : F (Sum.inr pB) = u := rfl
  have hFqB : F (Sum.inr pB.symm) = v := rfl
  set σ1 := σ0 * swap (Sum.inl pA) (Sum.inr pB) with hσ1
  set σ2 := σ1 * swap p q with hσ2
  set σ3 := removeFromCycle σ2 (Sum.inr pB) with hσ3
  set σ4 := removeFromCycle σ3 (Sum.inr pB.symm) with hσ4
  set α4 := α0 * swap (Sum.inr pB) (Sum.inr pB.symm) with hα4
  have hF1 : ∀ x, F (σ1 x) = F x := mulSwap_preserves F hF0 (by rw [hFpA, hFpB])
  have hF2 : ∀ x, F (σ2 x) = F x := mulSwap_preserves F hF1 (by rw [hFp, hFq])
  have hF3 : ∀ x, F (σ3 x) = F x := removeFromCycle_preserves F hF2 _
  have hF4 : ∀ x, F (σ4 x) = F x := removeFromCycle_preserves F hF3 _
  have e1 : ∀ x, x ≠ Sum.inl pA → x ≠ Sum.inr pB → σ1 x = σ0 x := fun x h1 h2 => by
    rw [hσ1, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2]
  have e1pA : σ1 (Sum.inl pA) = Sum.inr (MB.rot pB) := by
    rw [hσ1, Perm.mul_apply, swap_apply_left]
    rfl
  have e1pB : σ1 (Sum.inr pB) = Sum.inl (MA.rot pA) := by
    rw [hσ1, Perm.mul_apply, swap_apply_right]
    rfl
  have hp1 : p ≠ Sum.inl pA := hne_of_F _ _ (by rw [hFp, hFpA]; exact huv.symm)
  have hp2 : p ≠ Sum.inr pB := Sum.inl_ne_inr
  have hq1 : q ≠ Sum.inl pA := Sum.inr_ne_inl
  have hq2 : q ≠ Sum.inr pB := hne_of_F _ _ (by rw [hFq, hFpB]; exact huv.symm)
  have e1p : σ1 p = Sum.inl pA.symm := by
    rw [e1 p hp1 hp2, hp, hσ0l, perm_apply_inv_self]
  have e1q : σ1 q = Sum.inr pB.symm := by
    rw [e1 q hq1 hq2, hq, hσ0r, perm_apply_inv_self]
  -- the defect
  have hd1 : eulerDefect σ1 α0 = 0 := by
    rw [hσ1, eulerDefect_mulSwap_merge_of_not_rel (not_compSetoid_sumCongr pA pB), hdef0]
  set φ1 := σ1 * α0 with hφ1
  have hφp : φ1 (α0⁻¹ p) = Sum.inl pA.symm := by
    rw [hφ1, Perm.mul_apply, perm_apply_inv_self, e1p]
  have hφq : φ1 (α0⁻¹ q) = Sum.inr pB.symm := by
    rw [hφ1, Perm.mul_apply, perm_apply_inv_self, e1q]
  have hφqA : φ1 (Sum.inl pA.symm) = Sum.inr (MB.facePerm pB.symm) := by
    rw [hφ1, Perm.mul_apply, hα0l, SimpleGraph.Dart.symm_symm, e1pA, PlaneMap.facePerm_apply,
      SimpleGraph.Dart.symm_symm]
  have hagree : ∀ z, z ≠ pB.symm → φ1 (Sum.inr z) = Sum.inr (MB.facePerm z) := by
    intro z hz
    have hz' : Sum.inr z.symm ≠ (Sum.inr pB : GA.Dart ⊕ GB.Dart) := by
      intro h
      apply hz
      rw [← Sum.inr.inj h, SimpleGraph.Dart.symm_symm]
    rw [hφ1, Perm.mul_apply, hα0r, e1 _ Sum.inr_ne_inl hz', hσ0r, PlaneMap.facePerm_apply]
  have hseg : SameCycle φ1 (Sum.inr (MB.facePerm pB.symm)) (Sum.inr pB.symm) :=
    sameCycle_of_agree_until Sum.inr hagree (sameCycle_apply_left.2 (SameCycle.refl _ _))
  have hface : SameCycle φ1 (α0⁻¹ p) (α0⁻¹ q) := by
    have a1 : SameCycle φ1 (α0⁻¹ p) (Sum.inl pA.symm) := by
      rw [← hφp]; exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    have a2 : SameCycle φ1 (Sum.inl pA.symm) (Sum.inr (MB.facePerm pB.symm)) := by
      rw [← hφqA]; exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    have a3 : SameCycle φ1 (α0⁻¹ q) (Sum.inr pB.symm) := by
      rw [← hφq]; exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    exact a1.trans (a2.trans (hseg.trans a3.symm))
  have hd2 : eulerDefect σ2 α0 ≤ 0 :=
    (eulerDefect_mulSwap_le_of_face Sum.inl_ne_inr hface).trans hd1.le
  have hBne : (Sum.inr pB : GA.Dart ⊕ GB.Dart) ≠ Sum.inr pB.symm :=
    hne_of_F _ _ (by rw [hFpB, hFqB]; exact huv)
  have hd4 : eulerDefect σ4 α4 ≤ 0 :=
    (eulerDefect_mul_swap_right hBne ⟨1, by rw [zpow_one, hα0r]⟩).trans
      ((eulerDefect_removeFromCycle _ _ _).trans ((eulerDefect_removeFromCycle _ _ _).trans hd2))
  -- darts outside the kept set are fixed
  let P : GA.Dart ⊕ GB.Dart → Prop := fun x => x ≠ Sum.inr pB ∧ x ≠ Sum.inr pB.symm
  have hfix : ∀ x, ¬ P x → σ4 x = x ∧ α4 x = x := by
    intro x hx
    have hx' : x = Sum.inr pB ∨ x = Sum.inr pB.symm := by
      by_contra h
      push Not at h
      exact hx h
    rcases hx' with rfl | rfl
    · refine ⟨removeFromCycle_fix (removeFromCycle_apply_self _ _) hBne, ?_⟩
      rw [hα4, Perm.mul_apply, swap_apply_left, hα0r, SimpleGraph.Dart.symm_symm]
    · refine ⟨removeFromCycle_apply_self _ _, ?_⟩
      rw [hα4, Perm.mul_apply, swap_apply_right, hα0r]
  have hα : ∀ x, P x → sumDart (α4 x) = (sumDart x).symm := by
    intro x hx
    rw [hα4, Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2]
    exact sumDart_symm x
  have hinj : ∀ x y, P x → P y → sumDart x = sumDart y → x = y := by
    have key : ∀ (a : GA.Dart) (b : GB.Dart), a.toProd = b.toProd → b = pB ∨ b = pB.symm := by
      intro a b h
      obtain ⟨k1, k2⟩ := mem_inter_of_toProd_eq hA hB h
      rw [hK, Finset.mem_insert, Finset.mem_singleton] at k1 k2
      have h1 : a.fst = b.fst := congrArg Prod.fst h
      have h2 : a.snd = b.snd := congrArg Prod.snd h
      rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
      · exact absurd (k1.trans k2.symm) a.adj.ne
      · left
        exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext (h1 ▸ k1) (h2 ▸ k2))
      · right
        exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext (h1 ▸ k1) (h2 ▸ k2))
      · exact absurd (k1.trans k2.symm) a.adj.ne
    rintro (a | b) (a' | b') hx hy h <;> have h' := congrArg SimpleGraph.Dart.toProd h
    · exact congrArg Sum.inl ((SimpleGraph.Dart.ext_iff _ _).2 h')
    · rcases key a b' h' with rfl | rfl
      · exact absurd rfl hy.1
      · exact absurd rfl hy.2
    · rcases key a' b h'.symm with rfl | rfl
      · exact absurd rfl hx.1
      · exact absurd rfl hx.2
    · exact congrArg Sum.inr ((SimpleGraph.Dart.ext_iff _ _).2 h')
  have hsurj : ∀ e : (GA ⊔ GB).Dart, ∃ x, P x ∧ sumDart x = e := by
    intro e
    by_cases hAe : GA.Adj e.fst e.snd
    · exact ⟨Sum.inl ⟨e.toProd, hAe⟩, ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩, rfl⟩
    · have hBe : GB.Adj e.fst e.snd := ((SimpleGraph.sup_adj _ _ _ _).1 e.adj).resolve_left hAe
      refine ⟨Sum.inr ⟨e.toProd, hBe⟩, ⟨fun h => ?_, fun h => ?_⟩, rfl⟩
      · have := congrArg SimpleGraph.Dart.toProd (Sum.inr.inj h)
        apply hAe
        rw [show e.fst = u from congrArg Prod.fst this, show e.snd = v from congrArg Prod.snd this]
        exact hAuv
      · have := congrArg SimpleGraph.Dart.toProd (Sum.inr.inj h)
        apply hAe
        rw [show e.fst = v from congrArg Prod.fst this, show e.snd = u from congrArg Prod.snd this]
        exact hAuv.symm
  -- the cycle count
  have c1 : cycleCount σ1 + 1 = cycleCount σ0 :=
    cycleCount_mul_swap_of_not_sameCycle (π := σ0) (not_sameCycle_sumCongr pA pB)
  have hnsc : ¬ SameCycle σ1 p q := by
    let g : GA.Dart ⊕ GB.Dart → V × Bool :=
      fun x => (F x, if F x = v then Sum.isLeft x else true)
    have hg : ∀ x, g (σ1 x) = g x := by
      intro x
      refine Prod.ext (hF1 x) ?_
      change (if F (σ1 x) = v then Sum.isLeft (σ1 x) else true) =
        (if F x = v then Sum.isLeft x else true)
      rw [hF1 x]
      split_ifs with hx
      · have hx1 : x ≠ Sum.inl pA := hne_of_F _ _ (by rw [hx, hFpA]; exact huv.symm)
        have hx2 : x ≠ Sum.inr pB := hne_of_F _ _ (by rw [hx, hFpB]; exact huv.symm)
        rw [e1 x hx1 hx2]
        rcases x with d | d <;> rfl
      · rfl
    intro h
    have := sameCycle_of_step (Setoid.ker g) (fun z => by rw [Setoid.ker_def]; exact (hg z).symm) h
    rw [Setoid.ker_def] at this
    have h2 := congrArg Prod.snd this
    change (if F p = v then Sum.isLeft p else true) = (if F q = v then Sum.isLeft q else true)
      at h2
    rw [hFp, hFq, ite_eq_left rfl, ite_eq_left rfl] at h2
    exact Bool.noConfusion h2
  have c2 : cycleCount σ2 + 1 = cycleCount σ1 := cycleCount_mul_swap_of_not_sameCycle hnsc
  have hpBp : (Sum.inr pB : GA.Dart ⊕ GB.Dart) ≠ p := Sum.inr_ne_inl
  have hpBq : (Sum.inr pB : GA.Dart ⊕ GB.Dart) ≠ q := fun h => hq2 h.symm
  have e2pB : σ2 (Sum.inr pB) = Sum.inl (MA.rot pA) := by
    rw [hσ2, Perm.mul_apply, swap_apply_of_ne_of_ne hpBp hpBq, e1pB]
  have c3 : cycleCount σ3 = cycleCount σ2 + 1 :=
    cycleCount_removeFromCycle (by rw [e2pB]; exact Sum.inl_ne_inr)
  have e2qB : σ2 (Sum.inr pB.symm) ≠ Sum.inr pB.symm := by
    by_cases hqq : (Sum.inr pB.symm : GA.Dart ⊕ GB.Dart) = q
    · rw [hqq, hσ2, Perm.mul_apply, swap_apply_right, e1p]
      exact Sum.inl_ne_inr
    · have hqp : (Sum.inr pB.symm : GA.Dart ⊕ GB.Dart) ≠ p := Sum.inr_ne_inl
      rw [hσ2, Perm.mul_apply, swap_apply_of_ne_of_ne hqp hqq,
        e1 _ Sum.inr_ne_inl (fun h => hBne h.symm), hσ0r]
      intro h
      apply hqq
      rw [hq]
      congr 1
      have h' := Sum.inr.inj h
      rw [Perm.eq_inv_iff_eq, h']
  have c4 : cycleCount σ4 = cycleCount σ3 + 1 := by
    refine cycleCount_removeFromCycle ?_
    rw [hσ3, removeFromCycle_apply _ (fun h => hBne h.symm)]
    have : σ2 (Sum.inr pB.symm) ≠ Sum.inr pB :=
      hne_of_F _ _ (by rw [hF2, hFqB, hFpB]; exact huv.symm)
    rw [ite_eq_right this]
    exact e2qB
  have hcom : Nat.card {v // (∃ u, GA.Adj v u) ∧ (∃ u, GB.Adj v u)} ≤ 2 := by
    have h := Nat.card_le_card_of_injective
      (fun w : {v // (∃ u, GA.Adj v u) ∧ (∃ u, GB.Adj v u)} =>
        (⟨w.1, hcommon _ w.2.1 w.2.2⟩ : ↥(A ∩ B)))
      (fun a b h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h'))
    have h2 : Nat.card ↥(A ∩ B) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hK, Finset.card_pair huv]
    omega
  have hout : 2 ≤ Nat.card {x // ¬ P x} := by
    have h := Nat.card_le_card_of_injective
      (fun b : Bool => (cond b ⟨Sum.inr pB, fun h => h.1 rfl⟩ ⟨Sum.inr pB.symm, fun h => h.2 rfl⟩ :
        {x // ¬ P x}))
      (by
        intro a b h
        cases a <;> cases b
        · rfl
        · exact absurd (congrArg Subtype.val h) (fun e => hBne e.symm)
        · exact absurd (congrArg Subtype.val h) hBne
        · rfl)
    simpa using h
  refine isPlanar_of_hypermap_sub P σ4 α4 hfix hd4 sumDart hα (fun x _ => hF4 x) hinj hsurj ?_
  omega

end Glue2

end LeanPool.K5MinorFreeChoosability
