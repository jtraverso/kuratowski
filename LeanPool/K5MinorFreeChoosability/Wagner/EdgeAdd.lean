/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.SmallPlanar
public import LeanPool.K5MinorFreeChoosability.Wagner.Facial

/-!
# Extending permutations along injections, and adding an edge inside a face

* `extPerm ι hι π`: a permutation of `D'` transported along an injection `ι : D' → D` and
  extended by the identity; it keeps the Euler defect (`eulerDefect_extPerm`).
* `exists_planeMap_of_hypermap`: the realisation lemma, keeping track of the rotation.
* `exists_planeMap_addEdge`: two corners on a common face of a plane map can be joined by a new
  edge; the rotation is unchanged away from the two corners.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

theorem perm_apply_inv_self {D : Type*} (π : Perm D) (x : D) : π (π⁻¹ x) = x := by simp

section Ext

variable {D D' : Type*} (ι : D' → D) (hι : Function.Injective ι)

open Classical in
/-- Transport a permutation along an injection and extend it by the identity. -/
noncomputable def extPerm (π : Perm D') : Perm D :=
  ofSubtype ((Equiv.ofInjective ι hι).permCongr π)

theorem extPerm_apply (π : Perm D') (z : D') : extPerm ι hι π (ι z) = ι (π z) := by
  classical
  unfold extPerm
  rw [ofSubtype_apply_of_mem _ ⟨z, rfl⟩]
  have : (⟨ι z, ⟨z, rfl⟩⟩ : Set.range ι) = Equiv.ofInjective ι hι z := rfl
  rw [this, permCongr_apply, symm_apply_apply]
  rfl

theorem extPerm_apply_of_not (π : Perm D') {d : D} (hd : d ∉ Set.range ι) :
    extPerm ι hι π d = d := by
  classical
  unfold extPerm
  exact ofSubtype_apply_of_not_mem _ hd

theorem extPerm_inv_apply (π : Perm D') (z : D') : (extPerm ι hι π)⁻¹ (ι z) = ι (π⁻¹ z) := by
  rw [Perm.inv_eq_iff_eq, extPerm_apply, perm_apply_inv_self]

theorem eulerDefect_extPerm [Finite D] (σ α : Perm D') :
    eulerDefect (extPerm ι hι σ) (extPerm ι hι α) = eulerDefect σ α := by
  classical
  unfold extPerm
  rw [eulerDefect_ofSubtype, eulerDefect_permCongr]

theorem cycleCount_extPerm [Finite D] (π : Perm D') :
    cycleCount (extPerm ι hι π) = cycleCount π + Nat.card {d // d ∉ Set.range ι} := by
  classical
  unfold extPerm
  rw [cycleCount_ofSubtype, cycleCount_permCongr]

end Ext

section Insert

variable {D : Type*} [DecidableEq D] {σ : Perm D} {h n : D}

theorem insertBefore_apply_of_eq {m : D} (hm : σ m = h) (hσn : σ n = n) (hhn : h ≠ n) :
    insertBefore σ h n m = n := by
  have : m = σ⁻¹ h := by rw [← hm]; simp
  rw [this]
  exact insertBefore_apply_pred hσn hhn

theorem insertBefore_apply_of_ne' {u : D} (h1 : σ u ≠ h) (h2 : u ≠ n) :
    insertBefore σ h n u = σ u :=
  insertBefore_apply_of_ne (fun e => h1 (by rw [e]; simp)) h2

end Insert

/-- If every step of `π` is matched by one or two steps of `φ`, cycles of `π` map into cycles
of `φ`. -/
theorem sameCycle_of_two_step {D D' : Type*} {π : Perm D'} {φ : Perm D} (f : D' → D)
    (hf : ∀ z, φ (f z) = f (π z) ∨ φ (φ (f z)) = f (π z)) {a b : D'} (h : SameCycle π a b) :
    SameCycle φ (f a) (f b) := by
  have := sameCycle_of_step (Setoid.comap f (SameCycle.setoid φ)) (fun z => by
    rw [Setoid.comap_rel]
    change SameCycle φ _ _
    rcases hf z with e | e
    · rw [← e]; exact ⟨1, by simp⟩
    · rw [← e]; exact ⟨2, by rw [zpow_two, Perm.mul_apply]⟩) h
  rwa [Setoid.comap_rel] at this

/-- **Realisation, keeping the rotation**: a hypermap of defect at most zero labelled
bijectively by the darts of `G`, compatibly with reversal and tails, with at most one rotation
cycle per non-isolated vertex, is a plane map of `G` with the transported rotation. -/
theorem exists_planeMap_of_hypermap {D : Type*} [Finite D] {V : Type*} [Finite V]
    {G : SimpleGraph V} (σ α : Perm D) (hdef : eulerDefect σ α ≤ 0) (τ : D → G.Dart)
    (hτ : Function.Bijective τ) (hα : ∀ d, τ (α d) = (τ d).symm)
    (hσ : ∀ d, (τ (σ d)).fst = (τ d).fst)
    (hc : cycleCount σ ≤ Nat.card {v // ∃ u, G.Adj v u}) :
    ∃ P : PlaneMap G, ∀ d, P.rot (τ d) = τ (σ d) := by
  classical
  let e := Equiv.ofBijective τ hτ
  have he : ∀ d, e d = τ d := fun _ => rfl
  have : Finite G.Dart := Finite.of_equiv D e
  have hpc : ∀ (π : Perm D) d, (e.permCongr π) d = τ (π (e.symm d)) := fun π d => by
    simp [Equiv.permCongr_apply, he]
  have hsymm : e.permCongr α = dartSymm G := by
    refine Equiv.ext fun d => ?_
    rw [hpc, hα, ← he, Equiv.apply_symm_apply]
    rfl
  have hfst : ∀ d, ((e.permCongr σ) d).fst = d.fst := fun d => by
    rw [hpc, hσ, ← he, Equiv.apply_symm_apply]
  have hcc : cycleCount (e.permCongr σ) ≤ Nat.card (Set.range fun d : G.Dart => d.fst) := by
    rw [cycleCount_permCongr, natCard_range_fst]
    exact hc
  refine ⟨⟨e.permCongr σ, ⟨hfst, fun d d' hdd => ?_⟩, ?_⟩, fun d => ?_⟩
  · exact sameCycle_of_cycleCount_le _ (fun d : G.Dart => d.fst) hfst hcc hdd
  · rw [← hsymm, eulerDefect_permCongr]
    exact le_antisymm hdef (eulerDefect_nonneg σ α)
  · change (e.permCongr σ) (e d) = τ (σ d)
    rw [hpc, Equiv.symm_apply_apply]

/-! ### Adding an edge inside a face -/

section AddEdge

variable {V : Type*} [Finite V] [DecidableEq V] {G G' : SimpleGraph V} (M : PlaneMap G) {u v : V}
  (hadj : ∀ a b, G'.Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u))

include hadj in
/-- The inclusion of darts. -/
def inclDart (z : G.Dart) : G'.Dart := ⟨z.toProd, (hadj _ _).2 (Or.inl z.adj)⟩

omit [Finite V] [DecidableEq V] in
include hadj in
theorem inclDart_injective : Function.Injective (inclDart hadj) := by
  intro z z' h
  have h' := congrArg SimpleGraph.Dart.toProd h
  exact (SimpleGraph.Dart.ext_iff _ _).2 h'

omit [Finite V] [DecidableEq V] in
include hadj in
theorem ne_of_addEdge : u ≠ v := by
  rintro rfl
  exact G'.loopless.irrefl u ((hadj u u).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))

omit [DecidableEq V] in
/-- **Adding an edge in a face.**  If the darts `p` (leaving `u`) and `q` (leaving `v`) lie on a
common face of a plane map of `G`, then `G + uv` has a plane map whose rotation agrees with the
old one except at the two darts preceding `p` and `q`. -/
theorem exists_planeMap_addEdge (huv : ¬ G.Adj u v) (p q : G.Dart) (hp : p.fst = u)
    (hq : q.fst = v) (hf : SameCycle M.facePerm p q) :
    ∃ P : PlaneMap G', ∀ z : G.Dart, z ≠ M.rot⁻¹ p → z ≠ M.rot⁻¹ q →
      P.rot (inclDart hadj z) = inclDart hadj (M.rot z) := by
  classical
  classical
  have := Fintype.ofFinite V
  have hne := ne_of_addEdge hadj
  set ι := inclDart hadj with hιdef
  have hι := inclDart_injective hadj
  let c : G'.Dart := ⟨(u, v), (hadj u v).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  let d : G'.Dart := ⟨(v, u), (hadj v u).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hcd : c ≠ d := fun e => hne (congrArg (fun z : G'.Dart => z.fst) e)
  have hc : c ∉ Set.range ι := by
    rintro ⟨z, hz⟩
    have h' : z.toProd = (u, v) := by have h' := congrArg SimpleGraph.Dart.toProd hz; exact h'
    have hadjz := z.adj
    rw [show z.fst = u from congrArg Prod.fst h', show z.snd = v from congrArg Prod.snd h']
      at hadjz
    exact huv hadjz
  have hd : d ∉ Set.range ι := by
    rintro ⟨z, hz⟩
    have h' : z.toProd = (v, u) := by have h' := congrArg SimpleGraph.Dart.toProd hz; exact h'
    have hadjz := z.adj
    rw [show z.fst = v from congrArg Prod.fst h', show z.snd = u from congrArg Prod.snd h']
      at hadjz
    exact huv hadjz.symm
  have hcover : ∀ e : G'.Dart, e ∈ Set.range ι ∨ e = c ∨ e = d := by
    intro e
    rcases (hadj e.fst e.snd).1 e.adj with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨⟨e.toProd, h⟩, rfl⟩
    · exact Or.inr (Or.inl ((SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext h1 h2)))
    · exact Or.inr (Or.inr ((SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext h1 h2)))
  have hpq : p ≠ q := fun e => hne (by rw [← hp, ← hq, e])
  have hpq' : M.rot⁻¹ p ≠ M.rot⁻¹ q := fun e => hpq (M.rot⁻¹.injective e)
  set σ0 := extPerm ι hι M.rot with hσ0
  set α0 := extPerm ι hι (dartSymm G) with hα0
  have hσ0c : σ0 c = c := extPerm_apply_of_not ι hι _ hc
  have hσ0d : σ0 d = d := extPerm_apply_of_not ι hι _ hd
  have hα0c : α0 c = c := extPerm_apply_of_not ι hι _ hc
  have hα0d : α0 d = d := extPerm_apply_of_not ι hι _ hd
  have hσ0ι : ∀ z, σ0 (ι z) = ι (M.rot z) := extPerm_apply ι hι _
  have hα0ι : ∀ z, α0 (ι z) = ι z.symm := extPerm_apply ι hι _
  have hιc : ∀ z, ι z ≠ c := fun z e => hc ⟨z, e⟩
  have hιd : ∀ z, ι z ≠ d := fun z e => hd ⟨z, e⟩
  set σ1 := insertBefore σ0 (ι p) c with hσ1
  set σ2 := insertBefore σ1 (ι q) d with hσ2
  have e1p : σ1 (ι (M.rot⁻¹ p)) = c :=
    insertBefore_apply_of_eq (by rw [hσ0ι, perm_apply_inv_self]) hσ0c (hιc p)
  have e1z : ∀ z, z ≠ M.rot⁻¹ p → σ1 (ι z) = ι (M.rot z) := fun z hz => by
    rw [insertBefore_apply_of_ne' _ (hιc z), hσ0ι]
    rw [hσ0ι]
    exact fun e => hz (by rw [← hι e]; simp)
  have e1c : σ1 c = ι p := insertBefore_apply_new
  have e1d : σ1 d = d := by
    rw [insertBefore_apply_of_ne' _ hcd.symm, hσ0d]
    rw [hσ0d]
    exact (hιd p).symm
  have e2q : σ2 (ι (M.rot⁻¹ q)) = d :=
    insertBefore_apply_of_eq (by rw [e1z _ hpq'.symm, perm_apply_inv_self]) e1d (hιd q)
  have e2z : ∀ z, z ≠ M.rot⁻¹ q → σ2 (ι z) = σ1 (ι z) := fun z hz => by
    refine insertBefore_apply_of_ne' ?_ (hιd z)
    intro e
    by_cases hzp : z = M.rot⁻¹ p
    · rw [hzp, e1p] at e
      exact hιc q e.symm
    · rw [e1z z hzp] at e
      exact hz (by rw [← hι e]; simp)
  have e2d : σ2 d = ι q := insertBefore_apply_new
  have e2c : σ2 c = ι p := by
    rw [insertBefore_apply_of_ne' _ hcd, e1c]
    rw [e1c]
    exact fun e => hpq (hι e)
  -- the face condition
  set φ := σ2 * α0 with hφ
  have hstep : ∀ z, φ (ι z) = ι (M.facePerm z) ∨ φ (φ (ι z)) = ι (M.facePerm z) := by
    intro z
    simp only [hφ, Perm.mul_apply, hα0ι, PlaneMap.facePerm_apply]
    by_cases hzq : z.symm = M.rot⁻¹ q
    · right
      rw [hzq, e2q, hα0d, e2d, perm_apply_inv_self]
    by_cases hzp : z.symm = M.rot⁻¹ p
    · right
      rw [e2z _ hzq, hzp, e1p, hα0c, e2c, perm_apply_inv_self]
    · left
      rw [e2z _ hzq, e1z _ hzp]
  have hpqφ : SameCycle φ (ι p) (ι q) := sameCycle_of_two_step ι hstep hf
  have hcφ : φ c = ι p := by rw [hφ, Perm.mul_apply, hα0c, e2c]
  have hdφ : φ d = ι q := by rw [hφ, Perm.mul_apply, hα0d, e2d]
  have hfcd : SameCycle φ c d := by
    have h1 : SameCycle φ c (ι p) := hcφ ▸ (sameCycle_apply_right.2 (SameCycle.refl φ c))
    have h2 : SameCycle φ d (ι q) := hdφ ▸ (sameCycle_apply_right.2 (SameCycle.refl φ d))
    exact h1.trans (hpqφ.trans h2.symm)
  -- the defect
  have hdef0 : eulerDefect σ0 α0 = 0 := by
    rw [hσ0, hα0, eulerDefect_extPerm]
    exact M.eulerDefect_eq_zero
  have hdef1 : eulerDefect σ1 α0 = 0 := by
    rw [hσ1, eulerDefect_insertBefore hσ0c hα0c (hιc p), hdef0]
  have hdef2 : eulerDefect σ2 α0 = 0 := by
    rw [hσ2, eulerDefect_insertBefore e1d hα0d (hιd q), hdef1]
  have hdef : eulerDefect σ2 (α0 * swap c d) ≤ 0 :=
    (eulerDefect_mulSwap_right_le hcd hα0c hα0d hfcd).trans hdef2.le
  -- the cycle count
  have hcard : Nat.card {e // e ∉ Set.range ι} ≤ 2 := by
    have : Function.Injective fun e : {e // e ∉ Set.range ι} => decide (e.1 = c) := by
      intro e e' h
      rcases hcover e.1 with h1 | h1 | h1
      · exact absurd h1 e.2
      · rcases hcover e'.1 with h2 | h2 | h2
        · exact absurd h2 e'.2
        · exact Subtype.ext (h1.trans h2.symm)
        · simp [h1, h2, Ne.symm hcd] at h
      · rcases hcover e'.1 with h2 | h2 | h2
        · exact absurd h2 e'.2
        · simp [h1, h2, Ne.symm hcd] at h
        · exact Subtype.ext (h1.trans h2.symm)
    have := Nat.card_le_card_of_injective _ this
    simpa using this
  have hcc : cycleCount σ2 ≤ Nat.card {w // ∃ t, G'.Adj w t} := by
    have h1 := cycleCount_insertBefore (σ := σ0) (h := ι p) hσ0c (hιc p)
    have h2 := cycleCount_insertBefore (σ := σ1) (h := ι q) e1d (hιd q)
    have h3 := cycleCount_extPerm ι hι M.rot
    rw [cycleCount_eq_card_nonisolated M.isRotationSystem] at h3
    have h4 : Nat.card {w // ∃ t, G.Adj w t} ≤ Nat.card {w // ∃ t, G'.Adj w t} :=
      Nat.card_le_card_of_injective (fun w => ⟨w.1, w.2.elim fun t ht =>
        ⟨t, (hadj _ _).2 (Or.inl ht)⟩⟩)
        (fun a b h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h'))
    rw [← hσ1] at h1
    rw [← hσ2] at h2
    rw [← hσ0] at h3
    omega
  -- the involution and the tails
  have hα : ∀ e, (α0 * swap c d) e = e.symm := by
    intro e
    rcases hcover e with ⟨z, rfl⟩ | rfl | rfl
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hιc z) (hιd z), hα0ι]
      rfl
    · rw [Perm.mul_apply, swap_apply_left, hα0d]
      rfl
    · rw [Perm.mul_apply, swap_apply_right, hα0c]
      rfl
  have hfst : ∀ e, (σ2 e).fst = e.fst := by
    intro e
    rcases hcover e with ⟨z, rfl⟩ | rfl | rfl
    · by_cases hzq : z = M.rot⁻¹ q
      · rw [hzq, e2q]
        change v = (M.rot⁻¹ q).fst
        rw [M.fst_rot_inv, hq]
      by_cases hzp : z = M.rot⁻¹ p
      · rw [e2z _ hzq, hzp, e1p]
        change u = (M.rot⁻¹ p).fst
        rw [M.fst_rot_inv, hp]
      · rw [e2z _ hzq, e1z _ hzp]
        exact M.isRotationSystem.fst_apply z
    · rw [e2c]; exact hp
    · rw [e2d]; exact hq
  obtain ⟨P, hP⟩ := exists_planeMap_of_hypermap σ2 (α0 * swap c d) hdef id Function.bijective_id
    hα hfst hcc
  refine ⟨P, fun z hzp hzq => ?_⟩
  have := hP (ι z)
  simp only [id] at this
  rw [this, e2z _ hzq, e1z _ hzp]

end AddEdge

end LeanPool.K5MinorFreeChoosability
