/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Wagner.Facial

/-!
# The ring of faces around a vertex

For a dart `a` of a plane map, the face to the left of the corner between `a` and `rot a`
runs `rot a, …, a.symm`.  `ringSet a` is the set of tails of the darts strictly between `rot a`
and `a.symm` on this face: the face boundary with the corner vertex `a.fst` and the endpoint
`a.snd` removed.  For a graph without separations of order at most two these sets form a
"necklace" around the vertex `z = a.fst`:

* `ringSet_mem_snd_rot`: `(rot a).snd ∈ ringSet a`;
* `not_mem_ringSet_fst`, `not_mem_ringSet_snd`: `z ∉ ringSet a` and `a.snd ∉ ringSet a`;
* `connSet_ringSet`: `ringSet a` is connected;
* `touch_ringSet_rot`: `ringSet (rot a)` touches `ringSet a`;
* `disjoint_ringSet`: sets of different darts at `z` are disjoint.

The union of the necklace is the face cycle around `z` after deleting `z`.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*} [DecidableEq V] [Finite V] {G : SimpleGraph V}

namespace PlaneMap

variable (M : PlaneMap G)

omit [DecidableEq V] [Finite V] in
theorem sameCycle_face_rot_symm (a : G.Dart) : SameCycle M.facePerm (M.rot a) a.symm := by
  have h : SameCycle M.facePerm a.symm (M.rot a) :=
    ⟨1, by rw [zpow_one, facePerm_apply, SimpleGraph.Dart.symm_symm]⟩
  exact h.symm

omit [DecidableEq V] in
theorem exists_faceLen (a : G.Dart) : ∃ n : ℕ, (M.facePerm ^ n) (M.rot a) = a.symm := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨i, -, hi⟩ := (M.sameCycle_face_rot_symm a).exists_pow_eq'
  exact ⟨i, hi⟩

open Classical in
/-- The number of face steps from `rot a` to `a.symm`. -/
noncomputable def faceLen (a : G.Dart) : ℕ := Nat.find (M.exists_faceLen a)

theorem faceLen_spec (a : G.Dart) : (M.facePerm ^ M.faceLen a) (M.rot a) = a.symm := by
  classical
  exact Nat.find_spec (M.exists_faceLen a)

theorem faceLen_min (a : G.Dart) {n : ℕ} (h : n < M.faceLen a) :
    (M.facePerm ^ n) (M.rot a) ≠ a.symm := by
  classical
  exact Nat.find_min (M.exists_faceLen a) h

/-- The tails of the face darts strictly between `rot a` and `a.symm`. -/
noncomputable def ringSet (a : G.Dart) : Finset V :=
  (Finset.Ico 1 (M.faceLen a)).image fun n => ((M.facePerm ^ n) (M.rot a)).fst

theorem mem_ringSet {a : G.Dart} {v : V} :
    v ∈ M.ringSet a ↔ ∃ n, 1 ≤ n ∧ n < M.faceLen a ∧ ((M.facePerm ^ n) (M.rot a)).fst = v := by
  simp [ringSet, and_assoc]

omit [DecidableEq V] [Finite V] in
theorem fst_facePerm_pow_succ (d : G.Dart) (n : ℕ) :
    ((M.facePerm ^ (n + 1)) d).fst = ((M.facePerm ^ n) d).snd := by
  rw [pow_succ', Perm.mul_apply, facePerm_apply, M.isRotationSystem.fst_apply]
  rfl

theorem faceLen_pos (a : G.Dart) : 0 < M.faceLen a := by
  rcases Nat.eq_zero_or_pos (M.faceLen a) with h | h
  · have := M.faceLen_spec a
    rw [h, pow_zero, Perm.one_apply] at this
    have hf := congrArg (fun d : G.Dart => d.fst) this
    simp only [M.isRotationSystem.fst_apply, SimpleGraph.Dart.symm_toProd, Prod.fst_swap] at hf
    exact absurd hf a.adj.ne
  · exact h

theorem facePerm_pow_ne_rot (a : G.Dart) {n : ℕ} (h0 : 0 < n) (hn : n < M.faceLen a) :
    (M.facePerm ^ n) (M.rot a) ≠ M.rot a := by
  intro h
  have := M.faceLen_spec a
  have e : M.faceLen a = (M.faceLen a - n) + n := by omega
  rw [e, pow_add, Perm.mul_apply, h] at this
  exact M.faceLen_min a (by omega) this

theorem one_lt_faceLen {a : G.Dart} (ha : M.rot a ≠ a) : 1 < M.faceLen a := by
  have h0 := M.faceLen_pos a
  by_contra h
  have h1 : M.faceLen a = 1 := by omega
  have := M.faceLen_spec a
  rw [h1, pow_one, facePerm_apply] at this
  -- `rot (rot a).symm = a.symm`, so `(rot a).snd = a.snd`
  have hf := congrArg (fun d : G.Dart => d.fst) this
  simp only [M.isRotationSystem.fst_apply, SimpleGraph.Dart.symm_toProd, Prod.fst_swap] at hf
  apply ha
  refine (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext (M.isRotationSystem.fst_apply a) hf)

theorem ringSet_mem_snd_rot {a : G.Dart} (ha : M.rot a ≠ a) : (M.rot a).snd ∈ M.ringSet a := by
  rw [mem_ringSet]
  refine ⟨1, le_rfl, M.one_lt_faceLen ha, ?_⟩
  have := M.fst_facePerm_pow_succ (M.rot a) 0
  simpa using this

variable {S : Finset V} (hS : ∀ u v, G.Adj u v → u ∈ S) (hsep : NoSmallSep G S)
  (hK : numComponents M.rot (dartSymm G) ≤ 1)
include hS hsep hK

theorem not_mem_ringSet_fst (a : G.Dart) : a.fst ∉ M.ringSet a := by
  rw [mem_ringSet]
  rintro ⟨n, h1, h2, h3⟩
  have hs : SameCycle M.facePerm ((M.facePerm ^ n) (M.rot a)) (M.rot a) :=
    sameCycle_pow_left.2 (SameCycle.refl _ _)
  have := M.eq_of_sameCycle_face_of_fst hS hsep hK hs
    (h3.trans (M.isRotationSystem.fst_apply a).symm)
  exact M.facePerm_pow_ne_rot a (by omega) h2 this

theorem not_mem_ringSet_snd (a : G.Dart) : a.snd ∉ M.ringSet a := by
  rw [mem_ringSet]
  rintro ⟨n, h1, h2, h3⟩
  have hs : SameCycle M.facePerm ((M.facePerm ^ n) (M.rot a)) a.symm :=
    sameCycle_pow_left.2 (M.sameCycle_face_rot_symm a)
  have := M.eq_of_sameCycle_face_of_fst hS hsep hK hs (by simpa using h3)
  exact M.faceLen_min a h2 this

omit hS hsep hK in
theorem connSet_ringSet {a : G.Dart} (ha : M.rot a ≠ a) : ConnSet G ↑(M.ringSet a) := by
  have h1 := M.one_lt_faceLen ha
  have key : ∀ m, 1 ≤ m → m < M.faceLen a →
      ConnSet G ↑((Finset.Ico 1 (m + 1)).image fun n => ((M.facePerm ^ n) (M.rot a)).fst) := by
    intro m hm1 hm2
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [show Finset.Ico 1 (0 + 1 + 1) = {1} by decide, Finset.image_singleton,
          Finset.coe_singleton]
        exact connSet_singleton G _
      · have e : (Finset.Ico 1 (m + 1 + 1)).image (fun n => ((M.facePerm ^ n) (M.rot a)).fst) =
            insert ((M.facePerm ^ (m + 1)) (M.rot a)).fst
              ((Finset.Ico 1 (m + 1)).image fun n => ((M.facePerm ^ n) (M.rot a)).fst) := by
          rw [Nat.Ico_succ_right_eq_insert_Ico (by omega), Finset.image_insert]
        rw [e, Finset.coe_insert]
        refine (ih hm (by omega)).insert_adj (b := ((M.facePerm ^ m) (M.rot a)).fst) ?_ ?_
        · simp only [Finset.coe_image, Finset.coe_Ico, Set.mem_image, Set.mem_Ico]
          exact ⟨m, ⟨hm, by omega⟩, rfl⟩
        · rw [M.fst_facePerm_pow_succ]
          exact ((M.facePerm ^ m) (M.rot a)).adj.symm
  have := key (M.faceLen a - 1) (by omega) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

omit hS hsep hK in
theorem touch_ringSet_rot {a : G.Dart} (ha : M.rot a ≠ a) :
    Touch G (M.ringSet (M.rot a)) (M.ringSet a) := by
  have ha' : M.rot (M.rot a) ≠ M.rot a := fun h => ha (M.rot.injective h)
  have h1 := M.one_lt_faceLen ha'
  set L := M.faceLen (M.rot a)
  refine ⟨((M.facePerm ^ (L - 1)) (M.rot (M.rot a))).fst, ?_, (M.rot a).snd,
    M.ringSet_mem_snd_rot ha, ?_⟩
  · rw [mem_ringSet]
    exact ⟨L - 1, by omega, by omega, rfl⟩
  · have hs := M.fst_facePerm_pow_succ (M.rot (M.rot a)) (L - 1)
    rw [Nat.sub_add_cancel (by omega), M.faceLen_spec] at hs
    have hadj := ((M.facePerm ^ (L - 1)) (M.rot (M.rot a))).adj
    rw [← hs] at hadj
    simpa using hadj

theorem disjoint_ringSet {a b : G.Dart} (hab : a ≠ b) (hfst : a.fst = b.fst) :
    Disjoint (M.ringSet a) (M.ringSet b) := by
  rw [Finset.disjoint_left]
  intro u hua hub
  have hua' := hua
  have hub' := hub
  rw [mem_ringSet] at hua' hub'
  obtain ⟨n, hn1, hn2, hn3⟩ := hua'
  obtain ⟨m, hm1, hm2, hm3⟩ := hub'
  have hrs := M.isRotationSystem
  have hdiff : ¬ SameCycle M.facePerm (M.rot a) (M.rot b) := by
    intro h
    exact hab (M.rot.injective (M.eq_of_sameCycle_face_of_fst hS hsep hK h
      (by rw [hrs.fst_apply, hrs.fst_apply, hfst])))
  have hzu : (M.rot a).fst ≠ ((M.facePerm ^ n) (M.rot a)).fst := by
    rw [hrs.fst_apply, hn3]
    intro h
    exact M.not_mem_ringSet_fst hS hsep hK a (h ▸ hua)
  rcases M.two_faces_share hS hsep hK (g₁ := M.rot a) (g₂ := M.rot b)
      (g₁' := (M.facePerm ^ n) (M.rot a)) (g₂' := (M.facePerm ^ m) (M.rot b))
      (by rw [hrs.fst_apply, hrs.fst_apply, hfst]) (by rw [hn3, hm3]) hzu
      ⟨n, by simp⟩ ⟨m, by simp⟩ hdiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hb : M.rot a = b := M.rot.injective h2
    rw [hn3, hb] at h1
    exact M.not_mem_ringSet_snd hS hsep hK b (h1 ▸ hub)
  · have ha' : M.rot b = a := M.rot.injective h2
    rw [hn3, ha'] at h1
    exact M.not_mem_ringSet_snd hS hsep hK a (h1 ▸ hua)

end PlaneMap

end LeanPool.K5MinorFreeChoosability
