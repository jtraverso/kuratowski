/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-!
# Interpretation of the counts, and a planar example

* `cycleCount_eq_card_nonisolated`: the cycles of a rotation system are the vertices that
  carry an edge;
* `numComponents_le_one_of_connected`: a rotation system of a connected graph has one
  component;
* `isPlanar_K4`: the complete graph `K_4` is planar (an explicit genus-zero rotation system,
  the tetrahedron, with `4` vertices, `6` edges and `4` triangular faces).  This shows that the
  notion of plane map is not vacuous beyond forests and edgeless graphs.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

/-- The cycles of a rotation system correspond to the non-isolated vertices. -/
theorem cycleCount_eq_card_nonisolated {σ : Perm G.Dart} (hσ : IsRotationSystem G σ) :
    cycleCount σ = Nat.card {v // ∃ u, G.Adj v u} := by
  unfold cycleCount numClasses
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift
    (fun d : G.Dart => (⟨d.fst, d.snd, d.adj⟩ : {v // ∃ u, G.Adj v u})) ?_) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (r_eq_of_sameCycle (r := id) (fun z => hσ.fst_apply z) h)
  · intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    exact Quotient.sound (hσ.sameCycle a b (congrArg Subtype.val hpq))
  · rintro ⟨v, u, h⟩
    exact ⟨Quotient.mk _ ⟨(v, u), h⟩, rfl⟩

/-- A rotation system of a connected graph has at most one component. -/
theorem numComponents_le_one_of_connected [Finite V] {σ : Perm G.Dart}
    (hσ : IsRotationSystem G σ) (hG : G.Connected) : numComponents σ (dartSymm G) ≤ 1 := by
  classical
  have := Fintype.ofFinite V
  have key : ∀ (u v : V) (p : G.Walk u v) (d e : G.Dart), d.fst = u → e.fst = v →
      compSetoid σ (dartSymm G) d e := by
    intro u v p
    induction p with
    | nil => exact fun d e hd he =>
        compSetoid_of_sameCycle_left (hσ.sameCycle d e (hd.trans he.symm))
    | @cons a b c h p ih =>
      intro d e hd he
      let x : G.Dart := ⟨(a, b), h⟩
      have h1 : compSetoid σ (dartSymm G) d x := compSetoid_of_sameCycle_left (hσ.sameCycle d x hd)
      have h2 : compSetoid σ (dartSymm G) x x.symm := compSetoid_right _ _ x
      exact (compSetoid _ _).trans h1 ((compSetoid _ _).trans h2 (ih x.symm e rfl he))
  have hsub : Subsingleton (Quotient (compSetoid σ (dartSymm G))) := by
    constructor
    intro p q
    induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    exact Quotient.sound (key _ _ (hG.preconnected a.fst b.fst).some a b rfl rfl)
  exact Finite.card_le_one_iff_subsingleton.2 hsub

/-- Counting classes from above: if every class has at most `k` elements, then
`|α| ≤ k * numClasses s`. -/
theorem card_le_mul_numClasses {α : Type*} [Finite α] (s : Setoid α) (k : ℕ)
    (hk : ∀ a, Nat.card {b // s a b} ≤ k) : Nat.card α ≤ k * numClasses s := by
  classical
  have := Fintype.ofFinite α
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := Quotient.mk s) (s := (Finset.univ : Finset α)) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hfib : ∀ q : Quotient s, (Finset.univ.filter fun a => Quotient.mk s a = q).card ≤ k := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
    refine le_trans ?_ (hk a)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact s.symm (Quotient.exact hb)
  have : ∑ q : Quotient s, (Finset.univ.filter fun a => Quotient.mk s a = q).card ≤
      ∑ q : Quotient s, k :=
    Finset.sum_le_sum fun q _ => hfib q
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  simp only [numClasses, Nat.card_eq_fintype_card]
  rw [Finset.card_univ] at hsum
  rw [mul_comm]
  omega

/-- If `π ^ k` is the identity, every cycle of `π` has at most `k` elements. -/
theorem card_sameCycle_le {α : Type*} [Finite α] (π : Perm α) (k : ℕ) (hk0 : 0 < k)
    (hk : ∀ a, (π ^ k) a = a) (a : α) : Nat.card {b // SameCycle π a b} ≤ k := by
  have hmod : ∀ i, (π ^ i) a = (π ^ (i % k)) a := by
    intro i
    conv_lhs => rw [← Nat.mod_add_div i k, pow_add, Perm.mul_apply, pow_mul]
    congr 1
    induction i / k with
    | zero => simp
    | succ n ih => rw [pow_succ, Perm.mul_apply, hk, ih]
  calc Nat.card {b // SameCycle π a b} ≤ Nat.card (Fin k) := by
        refine Nat.card_le_card_of_surjective (fun i : Fin k => ⟨(π ^ (i : ℕ)) a,
          ⟨(i : ℤ), by simp⟩⟩) ?_
        rintro ⟨b, hb⟩
        obtain ⟨i, hi⟩ := hb.exists_nat_pow_eq
        refine ⟨⟨i % k, Nat.mod_lt _ hk0⟩, Subtype.ext ?_⟩
        simp only
        rw [← hmod, hi]
    _ = k := Nat.card_fin k

/-! ### `K_4` is planar -/

/-- The rotation of the tetrahedron: `k4next v u` is the neighbour following `u` around `v`. -/
def k4next : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 2, 3, 1], ![3, 0, 0, 2], ![1, 3, 0, 0], ![2, 0, 1, 0]]

theorem k4next_ne : ∀ a b : Fin 4, a ≠ b → a ≠ k4next a b := by decide

/-- The rotation of the tetrahedron as a map on darts. -/
def k4rotFun (d : (⊤ : SimpleGraph (Fin 4)).Dart) : (⊤ : SimpleGraph (Fin 4)).Dart :=
  ⟨(d.fst, k4next d.fst d.snd), by simpa using k4next_ne d.fst d.snd d.adj.ne⟩

theorem k4rotFun_bijective : Function.Bijective k4rotFun := by decide

/-- The tetrahedral rotation system of `K_4`. -/
noncomputable def k4rot : Perm (⊤ : SimpleGraph (Fin 4)).Dart :=
  Equiv.ofBijective _ k4rotFun_bijective

theorem k4rot_apply (d : (⊤ : SimpleGraph (Fin 4)).Dart) : k4rot d = k4rotFun d := rfl

theorem k4rot_sameTail : ∀ d e : (⊤ : SimpleGraph (Fin 4)).Dart, d.fst = e.fst →
    e = d ∨ e = k4rotFun d ∨ e = k4rotFun (k4rotFun d) := by decide

theorem k4face_cube : ∀ d : (⊤ : SimpleGraph (Fin 4)).Dart,
    k4rotFun (k4rotFun (k4rotFun d.symm).symm).symm = d := by decide

theorem isRotationSystem_k4rot : IsRotationSystem (⊤ : SimpleGraph (Fin 4)) k4rot := by
  refine ⟨fun d => rfl, fun d e h => ?_⟩
  rcases k4rot_sameTail d e h with rfl | rfl | rfl
  · exact SameCycle.refl _ _
  · exact ⟨1, by simp [k4rot_apply]⟩
  · refine ⟨2, ?_⟩
    rw [zpow_two, Perm.mul_apply, k4rot_apply, k4rot_apply]

/-- `K_4` is planar. -/
theorem isPlanar_K4 : IsPlanar (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨⟨k4rot, isRotationSystem_k4rot, le_antisymm ?_ (eulerDefect_nonneg _ _)⟩⟩
  have hn : Nat.card (⊤ : SimpleGraph (Fin 4)).Dart = 12 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hα := card_dart_eq_two_mul (⊤ : SimpleGraph (Fin 4))
  have hσ : cycleCount k4rot = 4 := by
    rw [cycleCount_eq_card_nonisolated isRotationSystem_k4rot, Nat.card_eq_fintype_card]
    decide
  have hK := numComponents_le_one_of_connected isRotationSystem_k4rot
    (SimpleGraph.connected_top (V := Fin 4))
  have hφ : Nat.card (⊤ : SimpleGraph (Fin 4)).Dart ≤
      3 * cycleCount (k4rot * dartSymm (⊤ : SimpleGraph (Fin 4))) := by
    refine card_le_mul_numClasses _ 3 fun d => card_sameCycle_le _ 3 (by norm_num) (fun a => ?_) d
    simpa [pow_succ, k4rot_apply] using k4face_cube a
  unfold eulerDefect
  omega

end LeanPool.K5MinorFreeChoosability
