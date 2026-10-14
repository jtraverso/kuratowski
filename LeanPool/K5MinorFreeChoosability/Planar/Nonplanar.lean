/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.MinorClosed

/-!
# `K_5` and `K_{3,3}` are not planar

The face-length argument: in a rotation system of a simple graph of minimum degree at least
two, every face has length at least three (`three_le_card_face`), and at least four if the
graph is bipartite (`four_le_card_face`).  Combined with Euler's formula this rules out
genus zero for `K_5` (`20` darts, `5` vertices, `10` edges, at most `6` faces) and for
`K_{3,3}` (`18` darts, `6` vertices, `9` edges, at most `4` faces).

Together with the minor-closedness of planarity we obtain the forward direction of Wagner's
theorem: a finite planar graph has neither a `K_5` nor a `K_{3,3}` minor
(`cliqueMinorFree_five_of_isPlanar`, `k33MinorFree_of_isPlanar`).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

theorem le_natCard_of_list {D : Type*} [Finite D] {P : D → Prop} (l : List D) (hl : l.Nodup)
    (hP : ∀ x ∈ l, P x) : l.length ≤ Nat.card {x // P x} := by
  classical
  have := Fintype.ofFinite D
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← List.toFinset_card_of_nodup hl]
  exact Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hP x (List.mem_toFinset.1 hx)

/-- Every rotation cycle contains all darts at its vertex. -/
theorem card_neighbor_le_card_sameCycle [Finite V] {σ : Perm G.Dart}
    (hσ : IsRotationSystem G σ) (d : G.Dart) :
    Nat.card {u // G.Adj d.fst u} ≤ Nat.card {e // SameCycle σ d e} := by
  classical
  have := Fintype.ofFinite V
  refine Nat.card_le_card_of_injective (fun u => ⟨⟨(d.fst, u.1), u.2⟩,
    hσ.sameCycle d _ rfl⟩) fun u u' h => ?_
  have := congrArg (fun e : {e // SameCycle σ d e} => e.1.snd) h
  exact Subtype.ext this

section Faces

variable {σ : Perm G.Dart} (hσ : IsRotationSystem G σ)
include hσ

theorem facePerm_fst (d : G.Dart) : ((σ * dartSymm G) d).fst = d.snd := by
  simp [hσ.fst_apply]

theorem face_ne_self (d : G.Dart) : (σ * dartSymm G) d ≠ d := fun h => by
  have := facePerm_fst hσ d
  rw [h] at this
  exact d.adj.ne this

theorem face_face_ne_self [Finite V] (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u})
    (d : G.Dart) : (σ * dartSymm G) ((σ * dartSymm G) d) ≠ d := by
  intro h
  set e := (σ * dartSymm G) d with he
  have h1 : e.fst = d.snd := facePerm_fst hσ d
  have h2 : e.snd = d.fst := by
    have := facePerm_fst hσ e
    rw [h] at this
    exact this.symm
  have hed : e = d.symm := SimpleGraph.Dart.ext_iff _ _ |>.2 (Prod.ext h1 h2)
  have hfix : σ d.symm = d.symm := by
    have : (σ * dartSymm G) d = σ d.symm := rfl
    rw [← this, ← he, hed]
  have hall : ∀ u (hu : G.Adj d.snd u), (⟨(d.snd, u), hu⟩ : G.Dart) = d.symm := by
    intro u hu
    exact ((hσ.sameCycle d.symm ⟨(d.snd, u), hu⟩ rfl).eq_of_left hfix).symm
  have hnt : Nontrivial {u // G.Adj d.snd u} :=
    Finite.one_lt_card_iff_nontrivial.1 (by have := hdeg d.snd; omega)
  obtain ⟨⟨u, hu⟩, ⟨u', hu'⟩, hne⟩ := hnt.exists_pair_ne
  have k1 := hall u hu
  have k2 := hall u' hu'
  apply hne
  have := congrArg (fun e : G.Dart => e.snd) (k1.trans k2.symm)
  exact Subtype.ext this

/-- In a simple graph of minimum degree at least two, every face has length at least three. -/
theorem three_le_card_face [Finite V] (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u})
    (d : G.Dart) : 3 ≤ Nat.card {e // SameCycle (σ * dartSymm G) d e} := by
  classical
  have := Fintype.ofFinite V
  set φ := σ * dartSymm G
  have n1 : φ d ≠ d := face_ne_self hσ d
  have n2 : φ (φ d) ≠ d := face_face_ne_self hσ hdeg d
  have n3 : φ (φ d) ≠ φ d := face_ne_self hσ (φ d)
  refine le_natCard_of_list [d, φ d, φ (φ d)] ?_ ?_
  · simp [Ne.symm n1, Ne.symm n2, Ne.symm n3]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-- In a bipartite simple graph of minimum degree at least two, every face has length at
least four. -/
theorem four_le_card_face [Finite V] (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u})
    (side : V → Bool) (hside : ∀ u v, G.Adj u v → side u ≠ side v) (d : G.Dart) :
    4 ≤ Nat.card {e // SameCycle (σ * dartSymm G) d e} := by
  classical
  have := Fintype.ofFinite V
  set φ := σ * dartSymm G
  have hs : ∀ e : G.Dart, side (φ e).fst = !side e.fst := by
    intro e
    rw [facePerm_fst hσ]
    have := hside _ _ e.adj
    revert this
    cases side e.fst <;> cases side e.snd <;> simp
  have n1 : φ d ≠ d := face_ne_self hσ d
  have n2 : φ (φ d) ≠ d := face_face_ne_self hσ hdeg d
  have n3 : φ (φ (φ d)) ≠ d := by
    intro h
    have := hs (φ (φ d))
    rw [h, hs, hs] at this
    cases side d.fst <;> simp at this
  have m1 : φ (φ d) ≠ φ d := face_ne_self hσ (φ d)
  have m2 : φ (φ (φ d)) ≠ φ d := face_face_ne_self hσ hdeg (φ d)
  have m3 : φ (φ (φ d)) ≠ φ (φ d) := face_ne_self hσ (φ (φ d))
  refine le_natCard_of_list [d, φ d, φ (φ d), φ (φ (φ d))] ?_ ?_
  · simp [Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm m1, Ne.symm m2, Ne.symm m3]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2
        (sameCycle_apply_right.2 (SameCycle.refl _ _)))

end Faces

theorem one_le_numComponents {D : Type*} [Finite D] [Nonempty D] (σ α : Perm D) :
    1 ≤ numComponents σ α := by
  have : Nonempty (Quotient (compSetoid σ α)) := ⟨Quotient.mk _ (Classical.arbitrary D)⟩
  exact Nat.card_pos

/-- `K_5` is not planar. -/
theorem not_isPlanar_K5 : ¬ IsPlanar (⊤ : SimpleGraph (Fin 5)) := by
  rintro ⟨P⟩
  have h0 := P.eulerDefect_eq_zero
  have hn : Nat.card (⊤ : SimpleGraph (Fin 5)).Dart = 20 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hdeg : ∀ v : Fin 5, 4 ≤ Nat.card {u // (⊤ : SimpleGraph (Fin 5)).Adj v u} := by
    intro v
    rw [Nat.card_eq_fintype_card]
    revert v
    decide
  have hα := card_dart_eq_two_mul (⊤ : SimpleGraph (Fin 5))
  have hσ : 4 * cycleCount P.rot ≤ Nat.card (⊤ : SimpleGraph (Fin 5)).Dart :=
    mul_numClasses_le _ 4 fun d =>
      (hdeg d.fst).trans (card_neighbor_le_card_sameCycle P.isRotationSystem d)
  have hφ : 3 * cycleCount (P.rot * dartSymm _) ≤ Nat.card (⊤ : SimpleGraph (Fin 5)).Dart :=
    mul_numClasses_le _ 3 fun d =>
      three_le_card_face P.isRotationSystem (fun v => le_trans (by norm_num) (hdeg v)) d
  have hne : Nonempty (⊤ : SimpleGraph (Fin 5)).Dart :=
    ⟨⟨((0 : Fin 5), (1 : Fin 5)), by decide⟩⟩
  have hK := one_le_numComponents P.rot (dartSymm (⊤ : SimpleGraph (Fin 5)))
  unfold eulerDefect at h0
  omega

/-- `K_{3,3}` is not planar. -/
theorem not_isPlanar_K33 : ¬ IsPlanar K33 := by
  rintro ⟨P⟩
  have h0 := P.eulerDefect_eq_zero
  have hn : Nat.card K33.Dart = 18 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hdeg : ∀ v, 3 ≤ Nat.card {u // K33.Adj v u} := by
    intro v
    rw [Nat.card_eq_fintype_card]
    revert v
    decide
  have hside : ∀ u v, K33.Adj u v → u.isLeft ≠ v.isLeft := by decide
  have hα := card_dart_eq_two_mul K33
  have hσ : 3 * cycleCount P.rot ≤ Nat.card K33.Dart :=
    mul_numClasses_le _ 3 fun d =>
      (hdeg d.fst).trans (card_neighbor_le_card_sameCycle P.isRotationSystem d)
  have hφ : 4 * cycleCount (P.rot * dartSymm _) ≤ Nat.card K33.Dart :=
    mul_numClasses_le _ 4 fun d =>
      four_le_card_face P.isRotationSystem (fun v => le_trans (by norm_num) (hdeg v)) _
        hside d
  have hne : Nonempty K33.Dart := ⟨⟨(Sum.inl 0, Sum.inr 0), by decide⟩⟩
  have hK := one_le_numComponents P.rot (dartSymm K33)
  unfold eulerDefect at h0
  omega

/-- A finite planar graph has no `K_5` minor. -/
theorem cliqueMinorFree_five_of_isPlanar [Finite V] (hG : IsPlanar G) : CliqueMinorFree G 5 :=
  fun ⟨M⟩ => not_isPlanar_K5 (isPlanar_of_minorModel hG M.toMinorModel)

/-- A finite planar graph has no `K_{3,3}` minor. -/
theorem k33MinorFree_of_isPlanar [Finite V] (hG : IsPlanar G) : K33MinorFree G :=
  fun ⟨M⟩ => not_isPlanar_K33 (isPlanar_of_minorModel hG M)

/-- **Wagner's theorem, forward direction**: a finite planar graph has neither a `K_5` nor a
`K_{3,3}` minor. -/
theorem noK5_noK33_of_isPlanar [Finite V] (hG : IsPlanar G) :
    ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G ∧ K33MinorFree G :=
  ⟨cliqueMinorFree_iff_not_isMinor.1 (cliqueMinorFree_five_of_isPlanar hG),
    k33MinorFree_of_isPlanar hG⟩

end LeanPool.K5MinorFreeChoosability
