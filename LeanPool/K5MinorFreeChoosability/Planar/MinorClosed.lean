/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Embedding
public import LeanPool.K5MinorFreeChoosability.Planar.MinorModel

/-!
# Planarity is closed under minors

`isPlanar_of_minorModel`: if `G` is a finite planar graph and `H` is a minor of `G` (given by a
branch-set model), then `H` is planar.  In particular planarity is invariant under graph
isomorphism and is inherited by subgraphs.

The proof performs deletions and contractions directly on the rotation system of `G`.  All
darts of `G` stay in one ambient type; a deleted or contracted edge becomes a pair of darts
fixed by both permutations.  We fix one dart of `G` for every dart of `H` (`cd`); every other
edge is processed in turn:

* an edge inside a branch set whose ends currently belong to different contracted vertices is
  *contracted*: the two rotation cycles are merged (`eulerDefect_merge`);
* every other edge is *deleted* (`eulerDefect_mul_swap_right`).

Contracted vertices are tracked by a representative function `r : V → V`.  The invariant
`RedInv` records that the rotation cycles are exactly the classes of `r`, that `r` only
identifies vertices of a common branch set, and that every processed edge inside a branch set
has its ends identified.  None of the operations increases the Euler defect, and the final
rotation, transported to the darts of `H`, is a rotation system of `H` of defect zero.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

namespace MinorModel

variable (M : MinorModel G H)

/-- Two vertices are equal or lie in a common branch set. -/
def SameBranch (u v : V) : Prop := u = v ∨ ∃ w, u ∈ M.branch w ∧ v ∈ M.branch w

theorem SameBranch.symm {M : MinorModel G H} {u v : V} (h : M.SameBranch u v) :
    M.SameBranch v u := by
  rcases h with rfl | ⟨w, hu, hv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨w, hv, hu⟩

theorem SameBranch.trans {M : MinorModel G H} {u v x : V} (h : M.SameBranch u v)
    (h' : M.SameBranch v x) : M.SameBranch u x := by
  rcases h with rfl | ⟨w, hu, hv⟩
  · exact h'
  rcases h' with rfl | ⟨w', hv', hx⟩
  · exact Or.inr ⟨w, hu, hv⟩
  · obtain rfl := M.eq_of_mem hv hv'
    exact Or.inr ⟨w, hu, hx⟩

/-- A dart is internal if both ends lie in the same branch set. -/
def Internal (z : G.Dart) : Prop := ∃ w, z.fst ∈ M.branch w ∧ z.snd ∈ M.branch w

theorem internal_symm {z : G.Dart} : M.Internal z.symm ↔ M.Internal z := by
  constructor <;> rintro ⟨w, h1, h2⟩ <;> exact ⟨w, h2, h1⟩

/-- A symmetric choice of one dart of `G` for every dart of `H`. -/
theorem exists_symm_choice :
    ∃ cd : H.Dart → G.Dart, (∀ e, (cd e).fst ∈ M.branch e.fst) ∧
      (∀ e, (cd e).snd ∈ M.branch e.snd) ∧ ∀ e, cd e.symm = (cd e).symm := by
  classical
  have hf : ∀ e : H.Dart, ∃ d : G.Dart, d.fst ∈ M.branch e.fst ∧ d.snd ∈ M.branch e.snd := by
    intro e
    obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent e.fst e.snd e.adj
    exact ⟨⟨(u, v), huv⟩, hu, hv⟩
  choose f hf1 hf2 using hf
  refine ⟨fun e => if WellOrderingRel e.fst e.snd then f e else (f e.symm).symm, ?_, ?_, ?_⟩
  · intro e
    dsimp only
    split_ifs
    · exact hf1 e
    · exact hf2 e.symm
  · intro e
    dsimp only
    split_ifs
    · exact hf2 e
    · exact hf1 e.symm
  · intro e
    have hne : e.fst ≠ e.snd := e.adj.ne
    have hs1 : e.symm.fst = e.snd := rfl
    have hs2 : e.symm.snd = e.fst := rfl
    dsimp only
    rw [hs1, hs2, SimpleGraph.Dart.symm_symm]
    by_cases h : WellOrderingRel e.fst e.snd
    · simp [h, asymm h]
    · have h' : WellOrderingRel e.snd e.fst := by
        rcases trichotomous_of WellOrderingRel e.fst e.snd with h1 | h1 | h1
        · exact absurd h1 h
        · exact absurd h1 hne
        · exact h1
      simp [h, h']

end MinorModel

section Reduction

variable (M : MinorModel G H) (inK : G.Dart → Prop)

/-- The invariant of the deletion–contraction process.  `A` is the set of remaining darts,
`(σ, α)` the current hypermap and `r` the representative of the current (contracted) vertex
of each original vertex. -/
structure RedInv (A : Finset G.Dart) (σ α : Perm G.Dart) (r : V → V) : Prop where
  fix_out : ∀ z, z ∉ A → σ z = z ∧ α z = z
  symm_mem : ∀ z ∈ A, z.symm ∈ A
  α_eq : ∀ z ∈ A, α z = z.symm
  r_rot : ∀ z, r (σ z).fst = r z.fst
  cyc : ∀ z ∈ A, ∀ w ∈ A, r z.fst = r w.fst → SameCycle σ z w
  r_inj : ∀ u v, r u = r v → M.SameBranch u v
  internal : ∀ z, z ∉ A → M.Internal z → r z.fst = r z.snd
  K_sub : ∀ z, inK z → z ∈ A

variable {M inK}

theorem r_eq_of_sameCycle {σ : Perm G.Dart} {r : V → V} (hr : ∀ z, r (σ z).fst = r z.fst)
    {a b : G.Dart} (h : SameCycle σ a b) : r a.fst = r b.fst := by
  have := sameCycle_of_step (Setoid.ker fun d : G.Dart => r d.fst)
    (fun z => by rw [Setoid.ker_def]; exact (hr z).symm) h
  rwa [Setoid.ker_def] at this

variable [DecidableEq V]

theorem removeFromCycle_preserves {D β : Type*} [DecidableEq D] (f : D → β) {π : Perm D}
    (hf : ∀ u, f (π u) = f u) (z : D) (u : D) : f (removeFromCycle π z u) = f u := by
  by_cases huz : u = z
  · rw [huz, removeFromCycle_apply_self]
  · rw [removeFromCycle_apply π huz]
    split_ifs with h
    · rw [hf z, ← h, hf u]
    · exact hf u

theorem removeFromCycle_fix {D : Type*} [DecidableEq D] {π : Perm D} {z u : D} (hu : π u = u)
    (huz : u ≠ z) : removeFromCycle π z u = u := by
  rw [removeFromCycle_apply π huz]
  simp [hu, huz]

/-- The common final part of a deletion or contraction step. -/
theorem RedInv.finish {A : Finset G.Dart} {σ α σ₁ : Perm G.Dart} {r r' : V → V}
    (I : RedInv M inK A σ α r) {z : G.Dart} (hzA : z ∈ A) (hzK : ¬ inK z)
    (hKsymm : ∀ z, inK z → inK z.symm)
    (P1 : ∀ u, u ∉ A → σ₁ u = u) (P2 : ∀ u, r' (σ₁ u).fst = r' u.fst)
    (P3 : ∀ u ∈ A, ∀ v ∈ A, u ≠ z → u ≠ z.symm → v ≠ z → v ≠ z.symm →
      r' u.fst = r' v.fst → SameCycle σ₁ u v)
    (P4 : ∀ u v, r' u = r' v → M.SameBranch u v)
    (P5 : ∀ u, (u ∉ A ∨ u = z ∨ u = z.symm) → M.Internal u → r' u.fst = r' u.snd) :
    RedInv M inK ((A.erase z).erase z.symm)
      (removeFromCycle (removeFromCycle σ₁ z) z.symm) (α * swap z z.symm) r' := by
  have hzz : z ≠ z.symm := (SimpleGraph.Dart.symm_ne z).symm
  have hz'A : z.symm ∈ A := I.symm_mem z hzA
  have hmem : ∀ u, u ∈ (A.erase z).erase z.symm ↔ u ≠ z.symm ∧ u ≠ z ∧ u ∈ A := by
    intro u; simp [Finset.mem_erase]
  have hz'K : ¬ inK z.symm := fun h => hzK (by simpa using hKsymm _ h)
  refine ⟨?_, ?_, ?_, ?_, ?_, P4, ?_, ?_⟩
  · intro u hu
    rw [hmem] at hu
    constructor
    · by_cases h1 : u = z.symm
      · rw [h1, removeFromCycle_apply_self]
      by_cases h2 : u = z
      · rw [h2]
        exact removeFromCycle_fix (removeFromCycle_apply_self _ _) hzz
      have h3 : u ∉ A := by tauto
      have h4 : σ₁ u = u := P1 u h3
      exact removeFromCycle_fix (removeFromCycle_fix h4 h2) h1
    · simp only [Perm.mul_apply]
      by_cases h1 : u = z.symm
      · rw [h1, swap_apply_right, I.α_eq z hzA]
      by_cases h2 : u = z
      · rw [h2, swap_apply_left, I.α_eq _ hz'A, SimpleGraph.Dart.symm_symm]
      have h3 : u ∉ A := by tauto
      rw [swap_apply_of_ne_of_ne h2 h1]
      exact (I.fix_out u h3).2
  · intro u hu
    rw [hmem] at hu ⊢
    refine ⟨fun h => hu.2.1 ?_, fun h => hu.1 ?_, I.symm_mem u hu.2.2⟩
    · simpa using congrArg SimpleGraph.Dart.symm h
    · simpa using congrArg SimpleGraph.Dart.symm h
  · intro u hu
    rw [hmem] at hu
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hu.2.1 hu.1, I.α_eq u hu.2.2]
  · intro u
    exact removeFromCycle_preserves (fun d : G.Dart => r' d.fst)
      (removeFromCycle_preserves (fun d : G.Dart => r' d.fst) P2 z) z.symm u
  · intro u hu v hv huv
    rw [hmem] at hu hv
    exact sameCycle_removeFromCycle hu.1 hv.1
      (sameCycle_removeFromCycle hu.2.1 hv.2.1
        (P3 u hu.2.2 v hv.2.2 hu.2.1 hu.1 hv.2.1 hv.1 huv))
  · intro u hu hint
    rw [hmem] at hu
    exact P5 u (by tauto) hint
  · intro u hu
    rw [hmem]
    refine ⟨fun h => hz'K (h ▸ hu), fun h => hzK (h ▸ hu), I.K_sub u hu⟩

/-- One step of the process: delete or contract the edge of a dart outside the kept set. -/
theorem RedInv.step [Finite G.Dart] {A : Finset G.Dart} {σ α : Perm G.Dart}
    {r : V → V} (I : RedInv M inK A σ α r) {z : G.Dart} (hzA : z ∈ A) (hzK : ¬ inK z)
    (hKsymm : ∀ z, inK z → inK z.symm) :
    ∃ σ' α' r', RedInv M inK ((A.erase z).erase z.symm) σ' α' r' ∧
      eulerDefect σ' α' ≤ eulerDefect σ α := by
  have hzz : z ≠ z.symm := (SimpleGraph.Dart.symm_ne z).symm
  have hz'A : z.symm ∈ A := I.symm_mem z hzA
  have hαz : α z = z.symm := I.α_eq z hzA
  have hαz' : α z.symm = z := by rw [I.α_eq _ hz'A, SimpleGraph.Dart.symm_symm]
  by_cases hcase : M.Internal z ∧ r z.fst ≠ r z.snd
  · -- contraction
    obtain ⟨hint, hne⟩ := hcase
    set a := z.fst
    set b := z.snd
    let r' : V → V := fun x => if r x = r b then r a else r x
    have hr'resp : ∀ x y, r x = r y → r' x = r' y := by
      intro x y h; simp only [r', h]
    have hr'a : r' a = r a := by simp [r']
    have hr'b : r' b = r a := by simp [r']
    have hnot : ¬ SameCycle σ z z.symm := fun h => hne (r_eq_of_sameCycle I.r_rot h)
    set σ₁ := σ * swap z z.symm
    have hzz₁ : SameCycle σ₁ z z.symm := sameCycle_mulSwap_of_not hnot
    have hle : ∀ {x y}, SameCycle σ x y → SameCycle σ₁ x y := by
      intro x y h
      have h' : SameCycle (σ₁ * swap z z.symm) x y := by
        simp only [σ₁]; rwa [mulSwap_mulSwap]
      exact sameCycle_of_sameCycle_mulSwap hzz₁ h'
    refine ⟨_, _, r', I.finish hzA hzK hKsymm (σ₁ := σ₁) ?_ ?_ ?_ ?_ ?_, ?_⟩
    · intro u hu
      have h1 : u ≠ z := fun h => hu (h ▸ hzA)
      have h2 : u ≠ z.symm := fun h => hu (h ▸ hz'A)
      simp only [σ₁, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2]
      exact (I.fix_out u hu).1
    · intro u
      simp only [σ₁, Perm.mul_apply]
      by_cases h1 : u = z
      · rw [h1, swap_apply_left]
        rw [hr'resp _ _ (I.r_rot z.symm)]
        change r' b = r' a
        rw [hr'a, hr'b]
      by_cases h2 : u = z.symm
      · rw [h2, swap_apply_right]
        rw [hr'resp _ _ (I.r_rot z)]
        change r' a = r' b
        rw [hr'a, hr'b]
      · rw [swap_apply_of_ne_of_ne h1 h2]
        exact hr'resp _ _ (I.r_rot u)
    · intro u hu v hv _ _ _ _ huv
      simp only [r'] at huv
      have hzb : r z.symm.fst = r b := rfl
      by_cases hu' : r u.fst = r b <;> by_cases hv' : r v.fst = r b <;>
        simp only [hu', hv', ↓reduceIte] at huv
      · exact hle (I.cyc u hu v hv (hu'.trans hv'.symm))
      · have k1 := hle (I.cyc u hu _ hz'A (hu'.trans hzb.symm))
        have k2 := hle (I.cyc _ hzA v hv huv)
        exact (k1.trans hzz₁.symm).trans k2
      · have k1 := hle (I.cyc u hu _ hzA huv)
        have k2 := hle (I.cyc _ hz'A v hv (hzb.trans hv'.symm))
        exact (k1.trans hzz₁).trans k2
      · exact hle (I.cyc u hu v hv huv)
    · intro u v huv
      have hab : M.SameBranch a b := by
        obtain ⟨w, h1, h2⟩ := hint
        exact Or.inr ⟨w, h1, h2⟩
      simp only [r'] at huv
      by_cases hu' : r u = r b <;> by_cases hv' : r v = r b <;>
        simp only [hu', hv', ↓reduceIte] at huv
      · exact I.r_inj u v (hu'.trans hv'.symm)
      · exact (I.r_inj u b hu').trans (hab.symm.trans (I.r_inj a v huv))
      · exact (I.r_inj u a huv).trans (hab.trans (I.r_inj b v hv'.symm))
      · exact I.r_inj u v huv
    · intro u hu hint'
      rcases hu with hu | rfl | rfl
      · exact hr'resp _ _ (I.internal u hu hint')
      · change r' a = r' b
        rw [hr'a, hr'b]
      · change r' b = r' a
        rw [hr'a, hr'b]
    · calc eulerDefect (removeFromCycle (removeFromCycle σ₁ z) z.symm) (α * swap z z.symm)
          ≤ eulerDefect (removeFromCycle σ₁ z) (α * swap z z.symm) :=
            eulerDefect_removeFromCycle _ _ _
        _ ≤ eulerDefect σ₁ (α * swap z z.symm) := eulerDefect_removeFromCycle _ _ _
        _ ≤ eulerDefect σ α := eulerDefect_merge hzz hαz hαz' hnot
  · -- deletion
    refine ⟨_, _, r, I.finish hzA hzK hKsymm (σ₁ := σ) (fun u hu => (I.fix_out u hu).1)
      I.r_rot (fun u hu v hv _ _ _ _ h => I.cyc u hu v hv h) I.r_inj ?_, ?_⟩
    · intro u hu hint
      rcases hu with hu | rfl | rfl
      · exact I.internal u hu hint
      · by_contra h
        exact hcase ⟨hint, h⟩
      · rw [M.internal_symm] at hint
        by_contra h
        exact hcase ⟨hint, fun h' => h (by simpa using h'.symm)⟩
    · have hs : SameCycle α z z.symm := ⟨1, by simp [hαz]⟩
      calc eulerDefect (removeFromCycle (removeFromCycle σ z) z.symm) (α * swap z z.symm)
          ≤ eulerDefect (removeFromCycle σ z) (α * swap z z.symm) :=
            eulerDefect_removeFromCycle _ _ _
        _ ≤ eulerDefect σ (α * swap z z.symm) := eulerDefect_removeFromCycle _ _ _
        _ ≤ eulerDefect σ α := eulerDefect_mul_swap_right hzz hs

omit [DecidableEq V] in
/-- Running the process until only kept darts remain. -/
theorem RedInv.reduce [Finite G.Dart] (hKsymm : ∀ z, inK z → inK z.symm) :
    ∀ (n : ℕ) (A : Finset G.Dart) (σ α : Perm G.Dart) (r : V → V), A.card = n →
      RedInv M inK A σ α r → ∃ A' σ' α' r', RedInv M inK A' σ' α' r' ∧
        (∀ z ∈ A', inK z) ∧ eulerDefect σ' α' ≤ eulerDefect σ α := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A σ α r hn I
  by_cases hall : ∀ z ∈ A, inK z
  · exact ⟨A, σ, α, r, I, hall, le_rfl⟩
  push Not at hall
  obtain ⟨z, hzA, hzK⟩ := hall
  obtain ⟨σ', α', r', I', hδ⟩ := I.step hzA hzK hKsymm
  have hcard : ((A.erase z).erase z.symm).card < n := by
    have hz'A : z.symm ∈ A.erase z :=
      Finset.mem_erase.2 ⟨SimpleGraph.Dart.symm_ne z, I.symm_mem z hzA⟩
    rw [Finset.card_erase_of_mem hz'A, Finset.card_erase_of_mem hzA]
    have : 0 < A.card := Finset.card_pos.2 ⟨z, hzA⟩
    omega
  obtain ⟨A'', σ'', α'', r'', I'', hK'', hδ''⟩ := ih _ hcard _ _ _ _ rfl I'
  exact ⟨A'', σ'', α'', r'', I'', hK'', hδ''.trans hδ⟩

end Reduction

/-- **Planarity is minor-closed**: a minor of a finite planar graph is planar. -/
theorem isPlanar_of_minorModel [Finite V] (hG : IsPlanar G) (M : MinorModel G H) :
    IsPlanar H := by
  classical
  have := Fintype.ofFinite V
  have hW : Finite W := M.finite_of_finite
  have hDfin : Finite G.Dart := inferInstance
  obtain ⟨P⟩ := hG
  obtain ⟨cd, hcd1, hcd2, hcds⟩ := M.exists_symm_choice
  have hcd_inj : Function.Injective cd := by
    intro e e' h
    have h1 : e.fst = e'.fst := M.eq_of_mem (hcd1 e) (h ▸ hcd1 e')
    have h2 : e.snd = e'.snd := M.eq_of_mem (hcd2 e) (h ▸ hcd2 e')
    exact SimpleGraph.Dart.ext_iff _ _ |>.2 (Prod.ext h1 h2)
  let inK : G.Dart → Prop := fun z => ∃ e, cd e = z
  have hKsymm : ∀ z, inK z → inK z.symm := by
    rintro z ⟨e, rfl⟩
    exact ⟨e.symm, hcds e⟩
  have I0 : RedInv M inK Finset.univ P.rot (dartSymm G) id := by
    refine ⟨fun z hz => absurd (Finset.mem_univ z) hz, fun z _ => Finset.mem_univ _,
      fun z _ => rfl, fun z => ?_, fun z _ w _ h => P.isRotationSystem.sameCycle z w h,
      fun u v h => Or.inl h, fun z hz => absurd (Finset.mem_univ z) hz,
      fun z _ => Finset.mem_univ _⟩
    simp [P.isRotationSystem.fst_apply z]
  obtain ⟨A, σ, α, r, I, hAK, hδ⟩ := RedInv.reduce hKsymm _ _ _ _ _ rfl I0
  rw [P.eulerDefect_eq_zero] at hδ
  have hmemA : ∀ e, cd e ∈ A := fun e => I.K_sub _ ⟨e, rfl⟩
  -- `r` is constant on branch sets
  have hconst : ∀ w x y, x ∈ M.branch w → y ∈ M.branch w → r x = r y := by
    intro w x y hx hy
    have hr := (M.connSet w).2 x hx y hy
    clear hy
    induction hr with
    | refl => rfl
    | @tail b c _ hbc ih =>
      obtain ⟨hadj, hb, hc⟩ := hbc
      refine ih.trans ?_
      let d : G.Dart := ⟨(b, c), hadj⟩
      have hdA : d ∉ A := by
        intro hd
        obtain ⟨e, he⟩ := hAK d hd
        have h1 : e.fst = w := M.eq_of_mem (hcd1 e) (by rw [he]; exact hb)
        have h2 : e.snd = w := M.eq_of_mem (hcd2 e) (by rw [he]; exact hc)
        exact e.adj.ne (h1.trans h2.symm)
      exact I.internal d hdA ⟨w, hb, hc⟩
  -- restriction to the kept darts
  have hσA : ∀ x, σ x ∈ A ↔ x ∈ A := by
    intro x
    constructor
    · intro h
      by_contra hx
      rw [(I.fix_out x hx).1] at h
      exact hx h
    · intro h
      by_contra hx
      have h2 : σ x = x := σ.injective (I.fix_out _ hx).1
      rw [h2] at hx
      exact hx h
  have hαA : ∀ x, α x ∈ A ↔ x ∈ A := by
    intro x
    constructor
    · intro h
      by_contra hx
      rw [(I.fix_out x hx).2] at h
      exact hx h
    · intro h
      rw [I.α_eq x h]
      exact I.symm_mem x h
  let g : H.Dart → {z // z ∈ A} := fun e => ⟨cd e, hmemA e⟩
  have hg : Function.Bijective g := by
    refine ⟨fun e e' h => hcd_inj (congrArg Subtype.val h), fun ⟨z, hz⟩ => ?_⟩
    obtain ⟨e, he⟩ := hAK z hz
    exact ⟨e, Subtype.ext he⟩
  let eA : {z // z ∈ A} ≃ H.Dart := (Equiv.ofBijective g hg).symm
  have heA_symm : ∀ e, eA.symm e = g e := fun e => rfl
  have heA : ∀ e, eA (g e) = e := fun e => eA.apply_symm_apply e
  let σH : Perm H.Dart := eA.permCongr (σ.subtypePerm hσA)
  have hσH : ∀ e, cd (σH e) = σ (cd e) := by
    intro e
    have : g (σH e) = σ.subtypePerm hσA (g e) := by
      simp only [σH, permCongr_apply, heA_symm]
      exact eA.symm_apply_apply _
    exact congrArg Subtype.val this
  have hαH : eA.permCongr (α.subtypePerm hαA) = dartSymm H := by
    ext1 e
    apply hcd_inj
    have : g (eA.permCongr (α.subtypePerm hαA) e) = α.subtypePerm hαA (g e) := by
      simp only [permCongr_apply, heA_symm]
      exact eA.symm_apply_apply _
    have h2 : cd (eA.permCongr (α.subtypePerm hαA) e) = α (cd e) := congrArg Subtype.val this
    rw [h2, dartSymm_apply, hcds]
    exact I.α_eq _ (hmemA e)
  refine ⟨⟨σH, ⟨fun e => ?_, fun e1 e2 h12 => ?_⟩, ?_⟩⟩
  · have h1 : r (cd (σH e)).fst = r (cd e).fst := by rw [hσH]; exact I.r_rot _
    rcases I.r_inj _ _ h1 with h | ⟨w, hw1, hw2⟩
    · exact M.eq_of_mem (hcd1 _) (h ▸ hcd1 e)
    · exact (M.eq_of_mem (hcd1 _) hw1).trans (M.eq_of_mem (hcd1 e) hw2).symm
  · have hr : r (cd e1).fst = r (cd e2).fst := hconst e1.fst _ _ (hcd1 e1) (h12 ▸ hcd1 e2)
    have hs := I.cyc _ (hmemA e1) _ (hmemA e2) hr
    have hs' : SameCycle (σ.subtypePerm hσA) (g e1) (g e2) := sameCycle_subtypePerm.2 hs
    rw [sameCycle_permCongr_iff eA, heA, heA] at hs'
    exact hs'
  · have hfin : Finite H.Dart := Finite.of_equiv _ eA
    have hle : eulerDefect σH (dartSymm H) ≤ 0 := by
      rw [← hαH, eulerDefect_permCongr, ← eulerDefect_ofSubtype,
        ofSubtype_subtypePerm _ (fun x hx => by_contra fun h => hx (I.fix_out x h).1),
        ofSubtype_subtypePerm _ (fun x hx => by_contra fun h => hx (I.fix_out x h).2)]
      exact hδ
    exact le_antisymm hle (eulerDefect_nonneg _ _)

/-- Planarity is invariant under isomorphism. -/
theorem isPlanar_of_iso [Finite V] (hG : IsPlanar G) (e : H ≃g G) : IsPlanar H :=
  isPlanar_of_minorModel hG (MinorModel.ofIso e)

/-- A minor of a planar graph is planar. -/
theorem IsPlanar.of_isMinor [Finite V] (hG : IsPlanar G) (h : IsMinor H G) : IsPlanar H :=
  h.elim fun M => isPlanar_of_minorModel hG M

end LeanPool.K5MinorFreeChoosability
